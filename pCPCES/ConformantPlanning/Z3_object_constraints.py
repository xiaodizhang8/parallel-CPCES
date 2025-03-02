import itertools
from z3 import *
from translate.pddl.conditions import Atom
from translate.pddl.conditions import NegatedAtom
from translate.pddl.conditions import Conjunction
from translate.pddl.conditions import Disjunction


class ObjectConstrains:
    def __init__(self, problem, candidate_plan, action_map, contexts=None):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts  # 只有warm starting才用得着context，普通的为None
        self.predicate_graph = None
        self.predicates_to_bool = dict()  # key: adjp4_4p3_4-0, value: Bool(adjp4_4p3_4-0)
        self.predicates_to_atom = dict()  # key: adjp4_4p3_4-0, value: adj p4_4 p3_4
        self.predicate_time_to_bool = dict()  # key: (predicate, timestamp), value: Bool(adjp4_4p3_4-0)
        self.constraints = list()

    def get_constraints_list(self):
        return self.constraints

    def regression(self, problem, candidate_plan, action_map):
        predicate_graph = dict()
        plan_length = len(candidate_plan)
        predicate_graph[plan_length] = problem.goal.get_predicate_set()

        for i in range(plan_length - 1, 0, -1):
            new_predicate_graph = set()
            step = candidate_plan[i].lower().split()
            step_name = step[0]
            step_args = step[1:]
            action = action_map['(' + step_name + ' ' + ' '.join(step_args) + ')']
            for add_effect in action.all_add_effects:
                conditions = add_effect[0]
                effect = add_effect[1]
                if effect in predicate_graph[i + 1]:
                    new_predicate_graph.add(effect)
                    new_predicate_graph = new_predicate_graph | set(conditions)

            for precondition in action.all_preconditions:
                new_predicate_graph.add(precondition)

            predicate_graph[i] = new_predicate_graph | predicate_graph[i + 1]
        self.predicate_graph = predicate_graph

    def add_regression_statements(self):
        asserted = set()
        for i in range(len(self.candidate_plan) - 1, -1, -1):
            step = self.candidate_plan[i].lower().split()
            step_name = step[0]
            step_args = step[1:]
            action = self.action_map['(' + step_name + ' ' + ' '.join(step_args) + ')']
            predicates = self.predicate_graph[i + 1]
            add_effects = set()  # 用于储存这个action中所有的add effect
            del_effects = set()  # 用于储存这个action中所有的del effect
            special_effects = set()  # 用于储存这个action中一些既属于Atom又属于NegatedAtom的effect
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
                special_items = set()

                special_add_effect_items = set()
                for add_effect in action.all_add_effects:
                    conditions = Conjunction(add_effect[0])
                    effect = add_effect[1]
                    if effect == special_effect:
                        special_add_effect_items.add(self.to_smt(conditions, i))
                special_items.add(Or(special_add_effect_items))

                special_del_effect_items = set()
                for del_effect in action.all_del_effects:
                    conditions = Conjunction(del_effect[0])
                    effect = del_effect[1]
                    if effect.negate() == special_effect:
                        special_del_effect_items.add(Not(self.to_smt(conditions, i)))
                special_items.add(And(special_del_effect_items))
                self.constraints.append(self.to_smt(special_effect, i + 1) == Or(special_items))
                asserted.add(self.to_smt(special_effect, i + 1))

            for add_effect in action.all_add_effects:
                conditions = Conjunction(add_effect[0])
                effect = add_effect[1]
                if effect in special_effects:
                    continue
                if effect in predicates:
                    self.constraints.append(
                        self.to_smt(effect, i + 1) == Or(self.to_smt(conditions, i), self.to_smt(effect, i)))
                    asserted.add(self.to_smt(effect, i + 1))

            for del_effect in action.all_del_effects:
                conditions = Conjunction(del_effect[0])
                effect = del_effect[1]
                if effect.negate() in special_effects:
                    continue
                if len(del_effect[0]) == 0:
                    self.constraints.append(self.to_smt(effect.negate(), i + 1) == False)
                    asserted.add(self.to_smt(effect.negate(), i + 1))
                    continue
                if effect.negate() in predicates or effect in predicates:
                    if len(del_effect[0]) != 0:
                        self.constraints.append(
                            self.to_smt(effect.negate(), i + 1) == And(self.to_smt(effect.negate(), i),
                                                                       Not(self.to_smt(conditions, i))))
                    else:
                        self.constraints.append(self.to_smt(effect.negate(), i + 1) == self.to_smt(effect.negate(), i))
                    asserted.add(self.to_smt(effect.negate(), i + 1))

            for predicate in predicates:
                if self.to_smt(predicate, i + 1) not in asserted and self.to_smt(predicate.negate(),
                                                                                 i + 1) not in asserted:
                    self.constraints.append(self.to_smt(predicate, i + 1) == self.to_smt(predicate, i))

    def add_precondition_statements(self):
        items = set()
        if self.candidate_plan is None:
            plan_length = 0
        else:
            plan_length = len(self.candidate_plan)
        self.predicates_to_bool['cpces_valcond0'] = Bool('cpces_valcond0')
        self.constraints.append(
            self.predicates_to_bool['cpces_valcond0'] == self.to_smt(self.problem.goal, plan_length))
        items.add(self.predicates_to_bool['cpces_valcond0'])
        for i in range(1, plan_length + 1):
            step = self.candidate_plan[-i].lower().split()
            step_name = step[0]
            step_args = step[1:]
            action = self.action_map['(' + step_name + ' ' + ' '.join(step_args) + ')']
            self.predicates_to_bool['cpces_valcond' + str(i)] = Bool('cpces_valcond' + str(i))
            self.constraints.append(
                self.predicates_to_bool['cpces_valcond' + str(i)] == self.to_smt(Conjunction(action.all_preconditions),
                                                                                 plan_length - i))
            items.add(self.predicates_to_bool['cpces_valcond' + str(i)])
        self.constraints.append(Not(And(items)))

    def add_initial_statements(self):
        items = set()
        for item in self.problem.init:
            if not item.predicate.startswith('='):
                items.add(self.to_smt(item, 0))
        for item in self.problem.initial_false:
            if not item.predicate.startswith('='):
                items.add(self.to_smt(item, 0))

        for unknown_group in self.problem.initial_probability_groups:
            unknown_items = set()
            sub_items = set()
            for item in unknown_group:
                sub_items.add(self.to_smt(item, 0))
            unknown_items.add(Or(sub_items))
            combinations = list(itertools.combinations(unknown_group, 2))
            for item in combinations:
                unknown_items.add(Or(Not(self.to_smt(item[0], 0)), Not(self.to_smt(item[1], 0))))
            items.add(And(unknown_items))

        for group in self.problem.disjunction_inits:
            disjunct_items = set()
            for item in group.parts:
                disjunct_items.add(self.to_smt(item, 0))
            items.add(Or(disjunct_items))
        self.constraints.append(And(items))

    def add_other_statements(self):
        all_possible_init = set()
        for predicate in self.problem.all_possible_initial:
            all_possible_init.add(predicate.get_formated_expression().replace(' ', '') + '-0')
        for predicate in self.predicates_to_bool.keys():
            if predicate.endswith('-0') and predicate not in all_possible_init:
                self.constraints.append(Not(self.predicates_to_bool[predicate]))


    def to_smt(self, predicate, timestamp):
        if isinstance(predicate, Atom):
            return self.Atom_to_smt(predicate, timestamp)
        elif isinstance(predicate, NegatedAtom):
            return self.NegatedAtom_to_smt(predicate, timestamp)
        elif isinstance(predicate, Conjunction):
            return self.Conjunction_to_smt(predicate, timestamp)
        elif isinstance(predicate, Disjunction):
            return self.Disjunction_to_smt(predicate, timestamp)
        else:
            return None

    def Atom_to_smt(self, predicate, timestamp):
        if isinstance(predicate, NegatedAtom):
            predicate = predicate.negate()
        if not isinstance(predicate, str):
            name = predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp)
            atom = predicate.predicate + ' ' + ' '.join(predicate.args)
        else:
            name = predicate.replace(' ', '') + '-' + str(timestamp)
            atom = predicate
        if name not in self.predicates_to_bool.keys():
            bool_item = Bool(name)
            self.predicates_to_bool[name] = bool_item
            self.predicates_to_atom[name] = predicate
            self.predicate_time_to_bool[(predicate, timestamp)] = bool_item
            return bool_item
        else:
            return self.predicates_to_bool[name]

    def NegatedAtom_to_smt(self, predicate, timestamp):
        if isinstance(predicate, NegatedAtom):
            predicate = predicate.negate()
        if not isinstance(predicate, str):
            name = predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp)
            atom = predicate.predicate + ' ' + ' '.join(predicate.args)
        else:
            name = predicate.replace(' ', '') + '-' + str(timestamp)
            atom = predicate
        if name not in self.predicates_to_bool.keys():
            bool_item = Bool(name)
            self.predicates_to_bool[name] = bool_item
            self.predicates_to_atom[name] = predicate
            self.predicate_time_to_bool[(predicate, timestamp)] = bool_item
            neg_bool_item = Not(bool_item)
            return neg_bool_item
        else:
            return Not(self.predicates_to_bool[name])

    def Conjunction_to_smt(self, conjunct, timestamp):
        items = set()
        for predicate in conjunct.parts:
            if isinstance(predicate, Atom):
                items.add(self.Atom_to_smt(predicate, timestamp))
            elif isinstance(predicate, NegatedAtom):
                items.add(self.NegatedAtom_to_smt(predicate, timestamp))
            elif isinstance(predicate, Conjunction):
                items.add(self.Conjunction_to_smt(predicate, timestamp))
            elif isinstance(predicate, Disjunction):
                items.add(self.Disjunction_to_smt(predicate, timestamp))
        if len(items) == 0:
            return And(True)
        else:
            return And(items)

    def Disjunction_to_smt(self, disjunct, timestamp):
        items = set()
        for predicate in disjunct.parts:
            if isinstance(predicate, Atom):
                items.add(self.Atom_to_smt(predicate, timestamp))
            elif isinstance(predicate, NegatedAtom):
                items.add(self.NegatedAtom_to_smt(predicate, timestamp))
            elif isinstance(predicate, Conjunction):
                items.add(self.Conjunction_to_smt(predicate, timestamp))
            elif isinstance(predicate, Disjunction):
                items.add(self.Disjunction_to_smt(predicate, timestamp))
        if len(items) == 0:
            return Or(True)
        else:
            return Or(items)
