import itertools
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.translate.pddl.conditions import Disjunction

class SMTStringConstraints:
    def __init__(self, problem, candidate_plan, action_map, contexts):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts
        self.predicate_graph = None
        self.declared_predicate = dict()
        self.predicates_to_bool = dict()  # key: adjp4_4p3_4-0, value: Bool(adjp4_4p3_4-0)
        self.predicates_to_atom = dict()  # key: adjp4_4p3_4-0, value: Atom(adj p4_4 p3_4)
        self.predicate_time_to_bool = dict()  # key: (predicate, timestamp), value: Bool(adjp4_4p3_4-0)
        self.constraint_string = ''

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

    def get_regression_assert(self):

        asserted = set()
        res = '(assert (and true '
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
                res += '(= ' + self.to_smt(special_effect, i + 1) + ' '
                res += '(or (or '
                for add_effect in action.all_add_effects:
                    conditions = Conjunction(add_effect[0])
                    effect = add_effect[1]
                    if effect == special_effect:
                        res += self.to_smt(conditions, i) + ' '
                        # self.declared_predicate = conditions.get_predicate(i, self.declared_predicate)
                res += ')'
                res += '(and '
                for del_effect in action.all_del_effects:
                    conditions = Conjunction(del_effect[0])
                    effect = del_effect[1]
                    if effect.negate() == special_effect:
                        res += '(not '
                        res += self.to_smt(conditions, i) + ' '
                        res += ' )'
                        # self.declared_predicate = conditions.get_predicate(i, self.declared_predicate)
                res += self.to_smt(special_effect, i) + ' '
                res += ')))'
                # self.declared_predicate = special_effect.get_predicate(i + 1, self.declared_predicate)
                # self.declared_predicate = special_effect.get_predicate(i, self.declared_predicate)
                asserted.add(self.to_smt(special_effect, i + 1))

            for add_effect in action.all_add_effects:
                conditions = Conjunction(add_effect[0])
                effect = add_effect[1]
                if effect in special_effects:
                    continue
                if effect in predicates:
                    res += '(= ' + self.to_smt(effect, i + 1) + ' '
                    res += '(or '
                    res += self.to_smt(conditions, i) + ' '
                    res += self.to_smt(effect, i) + ' '
                    res += '))'
                    # self.declared_predicate = effect.get_predicate(i + 1, self.declared_predicate)
                    # self.declared_predicate = effect.get_predicate(i, self.declared_predicate)
                    # self.declared_predicate = conditions.get_predicate(i, self.declared_predicate)
                asserted.add(self.to_smt(effect, i + 1))
            for del_effect in action.all_del_effects:
                conditions = Conjunction(del_effect[0])
                effect = del_effect[1]
                if effect.negate() in special_effects:
                    continue
                if len(del_effect[0]) == 0:
                    res += '(= '
                    res += self.to_smt(effect.negate(), i + 1) + ' '
                    res += 'false )'
                    # self.declared_predicate = effect.negate().get_predicate(i + 1, self.declared_predicate)
                    asserted.add(self.to_smt(effect.negate(), i + 1))
                    continue
                if effect.negate() in predicates or effect in predicates:
                    res += '(= ' + self.to_smt(effect.negate(), i + 1) + ' '
                    res += '(and '
                    res += self.to_smt(effect.negate(), i) + ' '
                    if len(del_effect[0]) != 0:
                        res += '(not '
                        res += self.to_smt(conditions, i) + ' '
                        res += ')'
                    res += '))'

                    # self.declared_predicate = effect.negate().get_predicate(i + 1, self.declared_predicate)
                    # self.declared_predicate = effect.negate().get_predicate(i, self.declared_predicate)
                    # self.declared_predicate = conditions.get_predicate(i, self.declared_predicate)
                    asserted.add(self.to_smt(effect.negate(), i + 1))

            for predicate in predicates:
                if self.to_smt(predicate, i + 1) not in asserted and self.to_smt(predicate.negate(), i + 1) not in asserted:
                    res += '(= ' + self.to_smt(predicate, i + 1) + ' '
                    res += self.to_smt(predicate, i) + ' '
                    res += ')'
                    # self.declared_predicate = predicate.get_predicate(i + 1, self.declared_predicate)
                    # self.declared_predicate = predicate.get_predicate(i, self.declared_predicate)
        res += '))\n'
        return res

    def get_precondition_assert(self):
        if self.candidate_plan is None:
            plan_length = 0
        else:
            plan_length = len(self.candidate_plan)
        res = ''
        res += '(declare-const cpces_valcond0 Bool)\n'
        res += '(assert (= cpces_valcond0 ' + self.to_smt(self.problem.goal, plan_length) + ' ))\n'
        # self.declared_predicate = self.problem.goal.get_predicate(plan_length, self.declared_predicate)
        for i in range(1, plan_length + 1):
            res += '(declare-const cpces_valcond' + str(i) + ' Bool)\n'
            step = self.candidate_plan[-i].lower().split()
            step_name = step[0]
            step_args = step[1:]
            action = self.action_map['(' + step_name + ' ' + ' '.join(step_args) + ')']
            res += '(assert (= cpces_valcond' + str(i) + ' ' + Conjunction(action.all_preconditions).to_smt(
                plan_length - i) + ' ))\n'
            # self.declared_predicate = Conjunction(action.all_preconditions).get_predicate(plan_length - i, self.declared_predicate)
        res += '(assert (not (and true '
        for i in range(0, plan_length + 1):
            res += 'cpces_valcond' + str(i) + ' '
        res += ')))\n'
        return res

    def get_true_precondition_assert(self):
        if self.candidate_plan is None:
            plan_length = 0
        else:
            plan_length = len(self.candidate_plan)
        res = ''
        res += '(declare-const cpces_valcond0 Bool)\n'
        res += '(assert (= cpces_valcond0 ' + self.to_smt(self.problem.goal, plan_length) + ' ))\n'
        # self.declared_predicate = self.problem.goal.get_predicate(plan_length, self.declared_predicate)
        for i in range(1, plan_length + 1):
            res += '(declare-const cpces_valcond' + str(i) + ' Bool)\n'
            step = self.candidate_plan[-i].lower().split()
            step_name = step[0]
            step_args = step[1:]
            action = self.action_map['(' + step_name + ' ' + ' '.join(step_args) + ')']
            res += '(assert (= cpces_valcond' + str(i) + ' ' + Conjunction(action.all_preconditions).to_smt(
                plan_length - i) + ' ))\n'
            # self.declared_predicate = Conjunction(action.all_preconditions).get_predicate(plan_length - i, self.declared_predicate)
        res += '(assert (and true '
        for i in range(0, plan_length + 1):
            res += 'cpces_valcond' + str(i) + ' '
        res += '))\n'
        return res

    def get_initial_assert(self):
        res = '(assert (and '
        for item in self.problem.init:
            predicate = item.predicate
            if not predicate.startswith('='):
                res += self.to_smt(item, 0) + ' '
                # if isinstance(item, Atom):
                #     self.declared_predicate = item.get_predicate(0, self.declared_predicate, 'true')
                # else:
                #     self.declared_predicate = item.get_predicate(0, self.declared_predicate, 'false')
        for item in self.problem.initial_false:
            predicate = item.predicate
            if not predicate.startswith('='):
                res += self.to_smt(item, 0) + ' '
                # if isinstance(item, Atom):
                #     self.declared_predicate = item.get_predicate(0, self.declared_predicate, 'true')
                # else:
                #     self.declared_predicate = item.get_predicate(0, self.declared_predicate, 'false')

        for unknown_group in self.problem.initial_probability_groups:
            res += '(and (or '
            for item in unknown_group:
                res += self.to_smt(item, 0) + ' '
                # self.declared_predicate = item.get_predicate(0, self.declared_predicate)
            res += ') '
            combinations = list(itertools.combinations(unknown_group, 2))
            for item in combinations:
                res += '(or (not ' + self.to_smt(item[0], 0) + ' ) (not ' + self.to_smt(item[1], 0) + ' )) '
            res += ')'
        for group in self.problem.disjunction_inits:
            res += '(or '
            for item in group.parts:
                res += self.to_smt(item, 0) + ' '
                # self.declared_predicate = item.get_predicate(0, self.declared_predicate)
            res += ')'
        res += '))\n'
        return res

    def get_other_assert(self):
        res = ''
        all_possible_init = set()
        for predicate in self.problem.all_possible_initial:
            all_possible_init.add(predicate.get_formated_expression().replace(' ', '') + '-0')
        for predicate in self.declared_predicate.keys():
            res += '(declare-const ' + predicate + ' Bool)\n'
            if predicate.endswith('-0') and predicate not in all_possible_init:
                res += '(assert (not ' + predicate + '))\n'
            # if type == 'true':
            #     res += '(assert ' + predicate + ' )\n'
            # elif type == 'false':
            #     res += '(assert (not ' + predicate + '))\n'
        return res


    def get_sample_tags_assert(self, sample_tags):
        res = '(assert (or '
        for group in sample_tags:
            if group is not None:
                for tag in group:
                    res += '(and '
                    for predicate in tag:
                        res += self.to_smt(predicate, 0) + ' '
                    res += ')'
        res += '))\n'
        return res

    def get_exception_sample_tag_assert(self, sample):
        res = '(assert (not (and \n'
        for predicate in sample:
            res += self.to_smt(predicate, 0) + ' '
        res += ')))'
        return res

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
        if not isinstance(predicate, str):
            name = predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp)
            atom = predicate.predicate + ' ' + ' '.join(predicate.args)
            self.declared_predicate[name.strip()] = predicate.predicate + ' ' + ' '.join(predicate.args)
        else:
            name = predicate.replace(' ', '') + '-' + str(timestamp)
            atom = predicate
        if atom not in self.predicates_to_atom.keys() and timestamp == 0:
            self.predicates_to_atom[name] = predicate
        return name


        # if not isinstance(predicate, str):
        #     res = predicate.predicate + ''.join(predicate.args)+'-'+str(timestamp)+' '
        #     self.declared_predicate[res.strip()] = predicate.predicate+' '+' '.join(predicate.args)
        # else:
        #     res = predicate.replace(' ','')
        # if res not in self.predicates_to_atom.keys():
        #     self.predicates_to_atom[res] = Bool(res)
        # return res


    def NegatedAtom_to_smt(self, predicate, timestamp):
        if not isinstance(predicate, str):
            name = '(not ' + predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp) + ')'
            atom = predicate.predicate + ' ' + ' '.join(predicate.args)
            self.declared_predicate[predicate.predicate + ''.join(predicate.args) + '-' + str(
                timestamp)] = predicate.predicate + ' ' + ' '.join(predicate.args)
        else:
            name = '(not ' + predicate.replace(' ', '') + '-' + str(timestamp) + ')'
            atom = predicate
        if atom not in self.predicates_to_atom.keys() and timestamp == 0:
            self.predicates_to_atom[name] = predicate

        return name
        # if not isinstance(predicate, str):
        #     res = '(not '+predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp)+') '
        #     self.declared_predicate[predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp)] = predicate.predicate+' '+' '.join(predicate.args)
        # else:
        #     res = '(not ' + predicate.replace(' ','') + ') '
        # if predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp) not in self.predicates_to_atom.keys():
        #     self.predicates_to_atom[predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp)] = Bool(predicate.predicate + ''.join(predicate.args) + '-' + str(timestamp))
        # return res

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
            return '(and true)'
        else:
            res = '(and '
            for i in items:
                res += i + ' '
            res += ') '
            return res

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
            return '(or true)'
        else:
            res = '(or '
            for i in items:
                res += i + ' '
            res += ') '
            return res