import itertools
import copy
from z3 import *
import pddl_parser
from translate.pddl.conditions import Truth
from translate.pddl.conditions import Atom
from translate.pddl.conditions import NegatedAtom
from translate.pddl.conditions import Conjunction
import sys
sys.path.append('translate')

'''
以下是产生单个counter example的方法
'''

declared_predicate = dict()


def extract_counter_example(sat_result):
    res = set()
    sat_result = sat_result.sexpr().split(')\n')
    for result in sat_result:
        result = result.split()
        predicate = result[1]
        boolean_value = result[4]
        if predicate.endswith('-0'):
            if 'true' in boolean_value:
                res.add(declared_predicate[predicate][1].strip())
    return res


def get_declare_assert(problem):
    res = ''
    all_possible_init = set()
    for predicate in problem.all_possible_initial:
        all_possible_init.add(predicate.get_formated_expression().replace(' ','')+'-0')
    for predicate, (type,_) in declared_predicate.items():
        res += '(declare-const ' + predicate + ' Bool)\n'
        if predicate.endswith('-0') and predicate not in all_possible_init:
            res += '(assert (not '+ predicate + '))\n'
        # if type == 'true':
        #     res += '(assert ' + predicate + ' )\n'
        # elif type == 'false':
        #     res += '(assert (not ' + predicate + '))\n'
    return res





def regression(problem, candidate_plan, action_map):
    predicate_graph = dict()
    plan_length = len(candidate_plan)
    predicate_graph[plan_length] = problem.goal.get_predicate_set()


    for i in range(plan_length-1, 0, -1):
        new_predicate_graph = set()
        step = candidate_plan[i].lower().split()
        step_name = step[0]
        step_args = step[1:]
        action = action_map['('+step_name+' '+' '.join(step_args)+')']
        for add_effect in action.all_add_effects:
            conditions = add_effect[0]
            effect = add_effect[1]
            if effect in predicate_graph[i+1]:
                new_predicate_graph.add(effect)
                new_predicate_graph = new_predicate_graph | set(conditions)

        for precondition in action.all_preconditions:
            new_predicate_graph.add(precondition)

        predicate_graph[i] = new_predicate_graph | predicate_graph[i+1]
    return predicate_graph


def get_regression_assert(predicate_graph, candidate_plan, action_map):
    global declared_predicate

    asserted = set()
    res = '(assert (and true '
    for i in range(len(candidate_plan)-1, -1, -1):
        step = candidate_plan[i].lower().split()
        step_name = step[0]
        step_args = step[1:]
        action = action_map['(' + step_name + ' ' + ' '.join(step_args) + ')']
        predicates = predicate_graph[i+1]
        add_effects = set() # 用于储存这个action中所有的add effect
        del_effects = set() # 用于储存这个action中所有的del effect
        special_effects = set() # 用于储存这个action中一些既属于Atom又属于NegatedAtom的effect
        # 这两个set中存的的predicate用于一种特殊情况的回归，即一个action中，一种condition推出了A，另一个condition推出了not A
        # 例子
        # A --> B, not A
        # C --> not B
        # D --> B
        # B' <--> (OR (or (A D)) (and (not C, B)))
        # 第一个or代表B变成true
        # 第二个or代表B保持True
        for add_effect in action.all_add_effects:
            add_effects.add(add_effect[1])
        for del_effect in action.all_del_effects:
            del_effects.add(del_effect[1])
        for add_effect in add_effects:
            if add_effect.negate() in del_effects:
                special_effects.add(add_effect)
        for special_effect in special_effects:
            res += '(= ' + special_effect.to_smt(i+1)
            res += '(or (or '
            for add_effect in action.all_add_effects:
                conditions = Conjunction(add_effect[0])
                effect = add_effect[1]
                if effect == special_effect:
                    res += conditions.to_smt(i)
                    declared_predicate = conditions.get_predicate(i, declared_predicate)
            res += ')'
            res += '(and '
            for del_effect in action.all_del_effects:
                conditions = Conjunction(del_effect[0])
                effect = del_effect[1]
                if effect.negate() == special_effect:
                    res += '(not '
                    res += conditions.to_smt(i)
                    res += ' )'
                    declared_predicate = conditions.get_predicate(i, declared_predicate)
            res += special_effect.to_smt(i)
            res += ')))'
            declared_predicate = special_effect.get_predicate(i + 1, declared_predicate)
            declared_predicate = special_effect.get_predicate(i, declared_predicate)
            asserted.add(special_effect.to_smt(i + 1))

        for add_effect in action.all_add_effects:
            conditions = Conjunction(add_effect[0])
            effect = add_effect[1]
            if effect in special_effects:
                continue
            if effect in predicates:
                res += '(= '+effect.to_smt(i+1)
                res += '(or '
                res += conditions.to_smt(i)
                res += effect.to_smt(i)
                res += '))'
                declared_predicate = effect.get_predicate(i+1, declared_predicate)
                declared_predicate = effect.get_predicate(i, declared_predicate)
                declared_predicate = conditions.get_predicate(i, declared_predicate)
            asserted.add(effect.to_smt(i+1))
        for del_effect in action.all_del_effects:
            conditions = Conjunction(del_effect[0])
            effect = del_effect[1]
            if effect.negate() in special_effects:
                continue
            if len(del_effect[0]) == 0:
                res += '(= '
                res += effect.negate().to_smt(i + 1)
                res += 'false )'
                declared_predicate = effect.negate().get_predicate(i + 1, declared_predicate)
                asserted.add(effect.negate().to_smt(i + 1))
                continue
            if effect.negate() in predicates or effect in predicates:
                res += '(= ' + effect.negate().to_smt(i + 1)
                res += '(and '
                res += effect.negate().to_smt(i) + ' '
                if len(del_effect[0]) != 0:
                    res += '(not '
                    res += conditions.to_smt(i)
                    res += ')'
                res += '))'

                declared_predicate = effect.negate().get_predicate(i + 1, declared_predicate)
                declared_predicate = effect.negate().get_predicate(i, declared_predicate)
                declared_predicate = conditions.get_predicate(i, declared_predicate)
                asserted.add(effect.negate().to_smt(i + 1))

        for predicate in predicates:
            if predicate.to_smt(i+1) not in asserted and predicate.negate().to_smt(i+1) not in asserted:
                res += '(= '+predicate.to_smt(i+1)
                res += predicate.to_smt(i)
                res += ')'
                declared_predicate = predicate.get_predicate(i + 1, declared_predicate)
                declared_predicate = predicate.get_predicate(i, declared_predicate)
    res += '))\n'
    return res


def get_precondition_assert(problem, candidate_plan, action_map):
    global declared_predicate
    if candidate_plan is None:
        plan_length = 0
    else:
        plan_length = len(candidate_plan)
    res = ''
    res += '(declare-const cpces_valcond0 Bool)\n'
    res += '(assert (= cpces_valcond0 ' + problem.goal.to_smt(plan_length)+'))\n'
    declared_predicate = problem.goal.get_predicate(plan_length, declared_predicate)
    for i in range(1, plan_length+1):
        res += '(declare-const cpces_valcond' + str(i) + ' Bool)\n'
        step = candidate_plan[-i].lower().split()
        step_name = step[0]
        step_args = step[1:]
        action = action_map['(' + step_name + ' ' + ' '.join(step_args) + ')']
        res += '(assert (= cpces_valcond'+str(i)+' '+Conjunction(action.all_preconditions).to_smt(plan_length-i)+'))\n'
        declared_predicate = Conjunction(action.all_preconditions).get_predicate(plan_length-i, declared_predicate)
    res += '(assert (not (and true '
    for i in range(0, plan_length + 1):
        res += 'cpces_valcond' + str(i) + ' '
    res += ')))\n'
    return res


def get_initial_assert(problem):
    global declared_predicate
    res = '(assert (and '
    for item in problem.init:
        predicate = item.predicate
        if not predicate.startswith('='):
            res += item.to_smt(0)
            if isinstance(item, Atom):
                declared_predicate = item.get_predicate(0, declared_predicate, 'true')
            else:
                declared_predicate = item.get_predicate(0, declared_predicate, 'false')
    for item in problem.initial_false:
        predicate = item.predicate
        if not predicate.startswith('='):
            res += item.to_smt(0)
            if isinstance(item, Atom):
                declared_predicate = item.get_predicate(0, declared_predicate, 'true')
            else:
                declared_predicate = item.get_predicate(0, declared_predicate, 'false')

    for unknown_group in problem.unknown_init_group:
        res += '(and (or '
        for item in unknown_group:
            res += item.to_smt(0)
            declared_predicate = item.get_predicate(0, declared_predicate)
        res += ') '
        combinations = list(itertools.combinations(unknown_group, 2))
        for item in combinations:
            res += '(or (not ' + item[0].to_smt(0)+') (not '+item[1].to_smt(0)+')) '
        res += ')'
    for group in problem.disjunction_inits:
        res += '(or '
        for item in group.parts:
            res += item.to_smt(0)
            declared_predicate = item.get_predicate(0, declared_predicate)
        res += ')'
    res += '))'
    return res


def generate_counter_example(problem, candidate_plan, action_map, additional_statements=None):
    global declared_predicate
    declared_predicate = dict()
    regression_assert = ''
    if candidate_plan is not None:
        predicate_graph = regression(problem, candidate_plan, action_map)
        # print(predicate_graph)
        regression_assert = get_regression_assert(predicate_graph, candidate_plan, action_map)
        # print(regression_assert)
    precondition_assert = get_precondition_assert(problem, candidate_plan, action_map)
    initial_assert = get_initial_assert(problem)
    # print(initial_assert)
    declare_assert = get_declare_assert(problem)
    # print(declare_assert)
    # declare_assert = ''
    # with open('testtrue.txt', 'r') as t:
    #     c = t.readlines()
    #     for i in c:
    #         declare_assert += i.strip() + '\n'
    constraint = declare_assert + regression_assert + precondition_assert + initial_assert
    if additional_statements != None:
        constraint += additional_statements
    # print(constraint)
    # with open('test.txt', 'w') as f:
    #     f.write(constraint)
    return call_SMT_solver(constraint)


def call_SMT_solver(constraint):
    solver = Solver()
    solver.from_string(constraint)
    # print(solver.check())
    if solver.check() == sat:
        counter_example = extract_counter_example(solver.model())
        # print(counter_example)
        return counter_example, constraint
    else:
        return None, constraint


def computeSingleCPCESCounterExample(problem, candidate_plan, action_map, additionl_statements=None):
    counter_example, constraint = generate_counter_example(problem, candidate_plan, action_map, additionl_statements)
    return counter_example, constraint

'''
以下是用于产生多个counter example的方法
'''


def computeMultipleCPCESCounterExample(problem, contexts, action_map):
    unknown_init = set([predicate for group in problem.unknown_init_group for predicate in group]) | problem.unknown_initial
    all_possible_initial = problem.all_possible_initial
    false_predicates = set()
    for distance_context in contexts.distance_contexts:
        remove_predicates = set()
        max_distance = 0
        for predicate in distance_context.keys():
            if predicate not in all_possible_initial: # 比如disposed, holding就属于不在all_possible_initial中
                remove_predicates.add(predicate)
            else:
                if predicate in unknown_init and distance_context[predicate] > max_distance: # 顺便计算context中的最大距离
                    max_distance = distance_context[predicate]
        for predicate, distance in distance_context.items():
            if distance < max_distance and predicate not in remove_predicates:
                false_predicates.add(predicate)

    predicates_map = dict() # 普通格式-Atom格式
    for predicate in problem.all_possible_initial | problem.initial_true | problem.initial_false:
        if isinstance(predicate, Atom):
            predicates_map[predicate.get_formated_expression()] = predicate
        else:
            predicates_map[predicate.negate().get_formated_expression()] = predicate.negate()

    additional_statement = ''
    for predicate in false_predicates:
        if predicate in unknown_init:
            additional_statement += '(assert (not ' + predicate.to_smt(0) + ' ))\n'
    counter_example, constraint = computeSingleCPCESCounterExample(problem=problem, candidate_plan=None, action_map=action_map, additionl_statements=additional_statement)
    sample_list = list()
    while counter_example is not None:
        sample_list.append(counter_example)
        for predicate in counter_example:
            if predicates_map[predicate] in unknown_init:
                additional_statement += '(assert (not '
                additional_statement += predicates_map[predicate].to_smt(0)
                additional_statement += '))\n'
        constraint += additional_statement
        counter_example, constraint = call_SMT_solver(constraint)
    return sample_list, None

'''
以下函数为入口函数和共用函数
'''

def computeCounterExample(problem, candidate_plan, action_map, contexts=None, additionl_statements=None, multiple=True):
    if multiple:
        return computeMultipleCPCESCounterExample(problem=problem, contexts=contexts, action_map=action_map)
    else:
        return computeSingleCPCESCounterExample(problem=problem, candidate_plan=candidate_plan, action_map=action_map, additionl_statements=additionl_statements)


def get_action_map(actions):
    res = dict()
    for action in actions:
        res[action.name] = action
    return res

# from translate.pddl_parser import pddl_file
# problem = pddl_file.open('./temp_domain.pddl', './temp_instance.pddl')
# candidate_plan = ['MAGIC', 'DUNK BOMB1 TOILET5', 'FLUSH TOILET2', 'DUNK BOMB14 TOILET2', 'FLUSH TOILET2', 'DUNK BOMB18 TOILET2', 'DUNK BOMB8 TOILET1']
#
# from instantiate import explore
# relaxed_reachable, atoms, actions, axioms, reachable_action = explore(problem)
# action_map = get_action_map(actions)
# counter_example, constraint = generate_counter_example(problem, candidate_plan, action_map)
# print(counter_example)
# print(problem.all_possible_initial)

