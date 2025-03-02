from pCPCES.translate.pddl.conditions import Truth
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.ConformantProbabilisticPlanning.MergedProblems import MergedProblems
from hashlib import sha256
import copy


def get_hash_code(s):
    return sha256(str(s).encode('utf-8')).hexdigest()

# def write_classical_instance_file_parallelly(problem, instance_file_path, merged_problems, tag_generator, index_hitting_set, all_projected_problems, contexts)

def write_classical_instance_file_by_hitting_set(problem, instance_file_path, merged_problems, tag_generator, index_hitting_set, all_projected_problems, contexts):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        obj = str(obj).split(': ')
        res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    for int_index in index_hitting_set:
        res += '  int' + str(int_index) + ' - inter\n'

    res += ')\n'
    res += '(:init\n'
    additional_predicates = set() # 有些predicate在context中，但是initial是已知的。这些predicate也要加上int
    constant_problem = merged_problems[0].constant_problem
    if len(constant_problem.constant_init) != 0:
        for predicate in constant_problem.constant_init:
            if predicate.predicate not in contexts.all_predicate_name_in_contexts:
                res += predicate.get_superfd_predicate()
            else:
                additional_predicates.add(predicate)
        res += '\n'

    for int_index in index_hitting_set:
        tag = tag_generator.index_tag_map[int_index]
        for predicate in tag:
            if isinstance(predicate, Atom):
                res += predicate.get_classical_problem_predicate_with_timestamp(int_index)
        for predicate in additional_predicates:
            if isinstance(predicate, Atom):
                res += predicate.get_classical_problem_predicate_with_timestamp(int_index)
        res += '(valid int' + str(int_index) + ')'
        res += '\n'
    res += ')\n'

    res += '(:goal (and \n'
    for tag_index in index_hitting_set:
        tag = tag_generator.index_tag_map[tag_index]
        problem_index = tag_generator.tag_subproblem_index_map[get_hash_code(tag)]
        projected_problem = all_projected_problems.all_projected_problems[problem_index]
        goal = projected_problem.goal
        res += '(and '
        for predicate in goal:
            res += predicate.get_classical_problem_predicate_with_timestamp(tag_index)
        res += '(valid int' + str(tag_index) + ')'
        res += ')'
    res += ')))'

    with open(instance_file_path, 'w') as f:
        f.write(res)


def write_classical_domain_file_by_hitting_set(problem, domain_file_path, contexts, index_hitting_set, tag_generator, all_projected_problems):
    index_hitting_set = list(index_hitting_set)

    # 虚伪的构造一个merged problems list，毕竟是经过挑选的一些problems，所以有些参数填None无所谓
    merged_problems = []
    for int_index in index_hitting_set:
        tag = tag_generator.index_tag_map[int_index]
        pro_index = tag_generator.tag_subproblem_index_map[get_hash_code(tag)]
        mp = MergedProblems(all_projected_problems, [pro_index], problem)
        mp.merge_problems()
        merged_problems.append(mp)


    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '    (:types  '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += 'inter - object'
    res += ')\n'
    res += '    (:predicates (true) '

    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            if predicate.split(' ')[0] in contexts.all_predicate_name_in_contexts:
                res += '(' + predicate + ' ?int - inter)'
            else:
                res += '(' + predicate + ')'
    res += '(valid ?int - inter)'
    res += ')\n'

    for action in problem.actions:
        res += '    (:action ' + action.name + '\n'
        res += '        :parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'
        res += '        :effect '

        effect_map = dict()
        truth_effect_list = list()
        for effect in action.effects:
            if type(effect.condition) != Truth:
                condition = effect.condition
                if condition in effect_map.keys():
                    effect_map[condition].append(effect.literal)
                else:
                    effect_map[condition] = [effect.literal]
            else:
                truth_effect_list.append(effect.literal)

        res_effect = ''
        for effect in truth_effect_list:
            effect_can_be_merged = predicates_can_be_merged(effect, contexts)
            if effect_can_be_merged:
                res_effect += '            ' + effect.get_CPP_merged_classical_problem_predicate(contexts) + '\n'
            else:
                res_effect += '(forall (?int - inter) '
                res_effect += effect.get_CPP_merged_classical_problem_predicate(contexts)
                res_effect += ')\n'

        if len(effect_map) != 0:
            for condition, effects in effect_map.items():
                condition_can_be_merged = predicates_can_be_merged(condition, contexts)
                effect_can_be_merged = predicates_can_be_merged(effects, contexts)
                if condition_can_be_merged and effect_can_be_merged:
                    res_effect += '            (when '
                    res_effect += condition.get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += Conjunction(effects).get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += ')\n'
                else:
                    res_effect += '            (forall (?int - inter) '
                    res_effect += '(when '
                    res_effect += condition.get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += Conjunction(effects).get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += '))\n'

        precondition = action.precondition
        if isinstance(precondition, Atom) or isinstance(precondition, NegatedAtom) or len(precondition.parts) != 0:
            is_constant_precondition = all_predicates_are_constant(precondition, contexts)
            if is_constant_precondition:
                res_effect += '            (forall (?int - inter)(when'
                res_effect += '(and (not ' + precondition.get_superfd_predicate() + ')) '
                res_effect += '(not (valid ?int))))\n'
            else:
                added_index = set()

                for iter_index in range(len(merged_problems)):
                    merged_problem = merged_problems[iter_index]
                    used_projected_problems = merged_problem.used_projected_problems
                    constant_precondition = merged_problem.constant_problem.precondition[action.name]
                    for case_index in range(len(used_projected_problems)):
                        problem_index = used_projected_problems[case_index]
                        projected_precondition = all_projected_problems.all_projected_problems[problem_index].precondition[action.name]
                        if len(projected_precondition) == 0:
                            continue
                        int_index = index_hitting_set[iter_index]
                        if int_index not in added_index:
                            res_precondition = '(and '
                            for predicate in projected_precondition:
                                res_precondition += '( ' + predicate.predicate + ' ' + ' '.join(predicate.args) + ' int' +str(int_index) + ') '
                            res_precondition += ')'
                            res_effect += '            (when'
                            res_effect += '(and (not ' + res_precondition + ')) '
                            res_effect += '(not (valid int' + str(int_index) + ')))\n'
                            added_index.add(int_index)
                    for predicate in constant_precondition:
                        res_effect += '            (forall (?int - inter)(when'
                        res_effect += '(and (not ' + predicate.get_superfd_predicate() + ')) '
                        res_effect += '(not (valid ?int))))\n'
                    # for case_index in range(len(used_projected_problems)):
                    #     problem_index = used_projected_problems[case_index]
                    #     int_index = index_hitting_set[iter_index]
                    #     if int_index not in added_index:
                    #         res_precondition = precondition.get_CPP_predicate_with_int(constant_precondition,
                    #                                                                    contexts,
                    #                                                                    int_index)
                    #         if res_precondition is not None:
                    #             res_effect += '            (when'
                    #             res_effect += '(and (not ' + res_precondition + ')) '
                    #             res_effect += '(not (valid int' + str(int_index) + ')))\n'
                    #         added_index.add(int_index)

        if res_effect != '':
            res += '(and\n'
            res += res_effect
            res += '        )\n'
        else:
            res += '()\n'
        res += '    )\n'
    res += ')'
    with open(domain_file_path, 'w') as f:
        f.write(res)

def write_classical_instance_file(problem, instance_file_path, merged_problems, probabilistic_tag_generator, sample_tags_history, contexts):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        obj = str(obj).split(': ')
        res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    written_int_index = set()
    for tag_history in sample_tags_history:
        for int_index in tag_history:
            if int_index not in written_int_index:
                res += '  int' + str(int_index) + ' - inter\n'
                written_int_index.add(int_index)


    res += ')\n'
    res += '(:init\n'
    additional_predicates = set()  # 有些predicate在context中，但是initial是已知的。这些predicate也要加上int
    constant_problem = merged_problems[0].constant_problem
    if len(constant_problem.constant_init) != 0:
        for predicate in constant_problem.constant_init:
            if predicate.predicate not in contexts.all_predicate_name_in_contexts:
                res += predicate.get_superfd_predicate()
            else:
                additional_predicates.add(predicate)
        res += '\n'

    for int_index in written_int_index:
        tag = probabilistic_tag_generator.index_tag_map[int_index]
        for predicate in tag:
            if isinstance(predicate, Atom):
                res += predicate.get_classical_problem_predicate_with_timestamp(int_index)
        for predicate in additional_predicates:
            if isinstance(predicate, Atom):
                res += predicate.get_classical_problem_predicate_with_timestamp(int_index)
        res += '(valid int' + str(int_index) + ')'
        res += '\n'
    res += ')\n'

    res += '(:goal (and \n'
    for problem_index in range(len(merged_problems)):
        mp = merged_problems[problem_index]
        goals = copy.deepcopy(mp.goal)
        res += '(or '
        for int_index in sample_tags_history[problem_index]:
            goal = goals[0]
            goals.remove(goal)
            res += '(and '
            for predicate in goal:
                res += predicate.get_classical_problem_predicate_with_timestamp(int_index)
            res += '(valid int' + str(int_index) + ')'
            res += ')'
        res += ')\n'
    res += ')))'
    # print(res)

    with open(instance_file_path, 'w') as f:
        f.write(res)

def write_classical_domain_file(problem, domain_file_path, merged_problems, contexts, sample_tags_history, all_projected_problems):
    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '    (:types  '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += 'inter - object'
    res += ')\n'
    res += '    (:predicates (true) '
    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            if predicate.split(' ')[0] in contexts.all_predicate_name_in_contexts:
                res += '(' + predicate + ' ?int - inter)'
            else:
                res += '(' + predicate + ')'
    res += '(valid ?int - inter)'
    res += ')\n'

    for action in problem.actions:
        res += '    (:action ' + action.name + '\n'
        res += '        :parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'
        res += '        :effect '

        # conditional_effects = action.effects
        # condition_effect_map = dict()
        # for conditional_effect in conditional_effects:
        #     condition = conditional_effect.condition
        #     effect = conditional_effect.literal
        #     if condition not in condition_effect_map.keys():
        #         condition_effect_map[condition] = []
        #     if effect not in condition_effect_map[condition]:
        #         condition_effect_map[condition].append(effect)

        effect_map = dict()
        truth_effect_list = list()
        for effect in action.effects:
            if type(effect.condition) != Truth:
                condition = effect.condition
                if condition in effect_map.keys():
                    effect_map[condition].append(effect.literal)
                else:
                    effect_map[condition] = [effect.literal]
            else:
                truth_effect_list.append(effect.literal)

        # res_effect = ''
        # for condition, effects in condition_effect_map.items():
        #     if isinstance(condition, Truth):
        #         res_effect += '            (forall (?int - inter)(and'
        #         for effect in effects:
        #             res_effect += effect.get_CPP_predicate()
        #         res_effect += '))\n'
        #     else:
        #         res_effect += '            (forall (?int - inter)(when'
        #         res_effect += condition.get_CPP_predicate()
        #         res_effect += '(and '
        #         for effect in effects:
        #             res_effect += effect.get_CPP_predicate()
        #         res_effect += ')))\n'
        res_effect = ''
        for effect in truth_effect_list:
            effect_can_be_merged = predicates_can_be_merged(effect, contexts)
            if effect_can_be_merged:
                res_effect += '            ' + effect.get_CPP_merged_classical_problem_predicate(contexts) + '\n'
            else:
                res_effect += '(forall (?int - inter) '
                res_effect += effect.get_CPP_merged_classical_problem_predicate(contexts)
                res_effect += ')\n'

        if len(effect_map) != 0:
            for condition, effects in effect_map.items():
                condition_can_be_merged = predicates_can_be_merged(condition, contexts)
                effect_can_be_merged = predicates_can_be_merged(effects, contexts)
                if condition_can_be_merged and effect_can_be_merged:
                    res_effect += '            (when '
                    res_effect += condition.get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += Conjunction(effects).get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += ')\n'
                else:
                    res_effect += '            (forall (?int - inter) '
                    res_effect += '(when '
                    res_effect += condition.get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += Conjunction(effects).get_CPP_merged_classical_problem_predicate(contexts)
                    res_effect += '))\n'


        # precondition = action.precondition
        # is_constant_precondition = all_predicates_are_constant(precondition, contexts)
        # if is_constant_precondition:
        #     res_effect += '            (forall (?int - inter)(when'
        #     res_effect += '(and (not ' + precondition.get_CPP_predicate() + ')) '
        #     res_effect += '(not (valid ?int))))\n'
        # else:
        #     added_index = set()
        #     for iter_index in range(len(merged_problems)):
        #         merged_problem = merged_problems[iter_index]
        #         used_projected_problems = merged_problem.used_projected_problems
        #         constant_precondition = merged_problem.constant_problem.precondition[action.name]
        #         for case_index in range(len(used_projected_problems)):
        #             problem_index = used_projected_problems[case_index]
        #             int_index = int_index_list[iter_index][case_index]
        #             if int_index not in added_index:
        #                 res_precondition = precondition.get_CPP_predicate_with_int(constant_precondition,
        #                                                                            contexts.contexts[problem_index], int_index)
        #                 if res_precondition is not None:
        #                     res_effect += '            (forall (?int - inter)(when'
        #                     res_effect += '(and (not ' + res_precondition + ')) '
        #                     res_effect += '(not (valid int' + str(int_index) + '))))\n'
        #                 added_index.add(int_index)

        precondition = action.precondition
        if isinstance(precondition, Atom) or isinstance(precondition, NegatedAtom) or len(precondition.parts) != 0:
            is_constant_precondition = all_predicates_are_constant(precondition, contexts)
            if is_constant_precondition:
                res_effect += '            (forall (?int - inter)(when'
                res_effect += '(and (not ' + precondition.get_superfd_predicate() + ')) '
                res_effect += '(not (valid ?int))))\n'
            else:
                added_index = set()
                for iter_index in range(len(merged_problems)):
                    merged_problem = merged_problems[iter_index]
                    used_projected_problems = merged_problem.used_projected_problems
                    constant_precondition = merged_problem.constant_problem.precondition[action.name]
                    for case_index in range(len(used_projected_problems)):
                        problem_index = used_projected_problems[case_index]
                        projected_precondition = all_projected_problems.all_projected_problems[problem_index].precondition[action.name]
                        if len(projected_precondition) == 0:
                            continue
                        int_index = sample_tags_history[iter_index][case_index]
                        if int_index not in added_index:
                            res_precondition = '(and '
                            for predicate in projected_precondition:
                                res_precondition += '( ' + predicate.predicate + ' ' + ' '.join(predicate.args) + ' int' +str(int_index) + ') '
                            res_precondition += ')'
                            res_effect += '            (when'
                            res_effect += '(and (not ' + res_precondition + ')) '
                            res_effect += '(not (valid int' + str(int_index) + ')))\n'
                            added_index.add(int_index)
                        # int_index = sample_tags_history[iter_index][case_index]
                        # if int_index not in added_index:
                        #     res_precondition = precondition.get_CPP_predicate_with_int(constant_precondition,
                        #                                                                contexts,
                        #                                                                int_index)
                        #     if res_precondition is not None:
                        #         res_effect += '            (when'
                        #         res_effect += '(and (not ' + res_precondition + ')) '
                        #         res_effect += '(not (valid int' + str(int_index) + ')))\n'
                        #     added_index.add(int_index)

        if res_effect != '':
            res += '(and\n'
            res += res_effect
            res += '        )\n'
        else:
            res += '()\n'
        res += '    )\n'
    res += ')'
    with open(domain_file_path, 'w') as f:
        f.write(res)

def predicates_can_be_merged(item, contexts):
    if isinstance(item, Atom):
        if item.predicate in contexts.all_predicate_name_in_contexts:
            return False
    elif isinstance(item, NegatedAtom):
        if item.negate().predicate in contexts.all_predicate_name_in_contexts:
            return False
    else:
        if isinstance(item, list):
            for i in item:
                if isinstance(i, Atom):
                    if i.predicate in contexts.all_predicate_name_in_contexts:
                        return False
                elif isinstance(i, NegatedAtom):
                    if i.negate().predicate in contexts.all_predicate_name_in_contexts:
                        return False
        else:
            for i in item.parts:
                if isinstance(i, Atom):
                    if i.predicate in contexts.all_predicate_name_in_contexts:
                        return False
                elif isinstance(i, NegatedAtom):
                    if i.negate().predicate in contexts.all_predicate_name_in_contexts:
                        return False
    return True

def all_predicates_are_constant(item, contexts):
    if isinstance(item, Atom) or isinstance(item, NegatedAtom):
        return atom_negatedatom_is_constant(item, contexts)
    else:
        return conjunction_disjunction_is_constant(item, contexts)

def atom_negatedatom_is_constant(item, contexts):
    if item.predicate not in contexts.all_predicate_name_in_contexts:
        return True
    else:
        return False

def conjunction_disjunction_is_constant(item, contexts):
    for i in item.parts:
        if isinstance(i, Atom) or isinstance(i, NegatedAtom):
            result =  atom_negatedatom_is_constant(i, contexts)
            if result is False:
                return False
        else:
            result = conjunction_disjunction_is_constant(i, contexts)
            if result is False:
                return False
    return True
