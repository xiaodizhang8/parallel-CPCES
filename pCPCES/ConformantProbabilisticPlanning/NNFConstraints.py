from nnf import And, Or, Var, false, true
import itertools
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.translate.pddl.conditions import Disjunction



class NNFConstraints:
    def __init__(self, problem, candidate_plan, action_map, contexts=None, merged_problem=None, tag_generator=None):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts  # 只有warm starting才用得着context，普通的为None
        self.merged_problem = merged_problem
        self.tag_generator = tag_generator
        self.predicate_graph = None
        self.predicates_to_bool = dict()  # key: adjp4_4p3_4-0, value: Bool(adjp4_4p3_4-0)
        self.predicates_to_atom = dict()  # key: adjp4_4p3_4-0, value: adj p4_4 p3_4
        self.predicate_time_to_bool = dict()  # key: (predicate, timestamp), value: Bool(adjp4_4p3_4-0)
        self.constraints = list()

    def add_initial_statements(self):
        items = set()
        for unknown_group in self.problem.initial_probability_groups:
            unknown_items = set()
            unknown_items.add(true)
            sub_items = set()
            sub_items.add(false)
            for item in unknown_group:
                sub_items.add(self.to_smt(item, 0))
            unknown_items.add(Or(sub_items))
            combinations = list(itertools.combinations(unknown_group, 2))
            for item in combinations:
                unknown_items.add(Or({~(self.to_smt(item[0], 0)), ~(self.to_smt(item[1], 0))}))
            items.add(And(unknown_items))

        for group in self.problem.disjunction_inits:
            disjunct_items = set()
            disjunct_items.add(false)
            for item in group.parts:
                disjunct_items.add(self.to_smt(item, 0))
            items.add(Or(disjunct_items))
        self.constraints.append(And(items))

    def add_projected_initial_statements(self):
        items = set()
        constant_items = set()
        for predicate in self.merged_problem.constant_init:
            constant_items.add(self.to_smt(predicate, 0))
        items.add(And(constant_items))

        for unknown_group in self.merged_problem.initial_probability_groups:
            single_items = set()
            single_items.add(false)
            for predicate in unknown_group.keys():
                single_items.add(self.to_smt(predicate, 0))
            items.add(Or(single_items))
            combinations = list(itertools.combinations(unknown_group.keys(), 2))
            pair_items = set()
            for pair in combinations:
                pair_items.add(Or({~self.to_smt(pair[0], 0), ~self.to_smt(pair[1], 0)}))
            items.add(And(pair_items))
        self.constraints.append(And(items))

    def add_projected_context_statements(self):
        items = set()
        for pro_index in self.merged_problem.used_projected_problems:
            tags_in_a_context = self.tag_generator.all_true_and_false_tags[pro_index]
            tag_items = set()
            for tag in tags_in_a_context:
                predicates_set = set()
                for predicate in tag:
                    predicates_set.add(self.to_smt(predicate, 0))
                tag_items.add(And(predicates_set))
            items.add(Or(tag_items))
        self.constraints.append(And(items))
        # print('context assert', And(items))



    def add_other_statements(self):
        all_possible_init = set()
        for predicate in self.problem.all_possible_initial:
            all_possible_init.add(predicate.get_formated_expression().replace(' ', '') + '-0')
        for predicate in self.predicates_to_bool.keys():
            if predicate.endswith('-0') and predicate not in all_possible_init:
                self.constraints.append(~(self.predicates_to_bool[predicate]))


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
            bool_item = Var(name)
            self.predicates_to_bool[name] = bool_item
            self.predicates_to_atom[name] = atom
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
            bool_item = Var(name)
            self.predicates_to_bool[name] = bool_item
            self.predicates_to_atom[name] = atom
            self.predicate_time_to_bool[(predicate, timestamp)] = bool_item
            neg_bool_item = ~(bool_item)
            return neg_bool_item
        else:
            return ~(self.predicates_to_bool[name])

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
            return And(true)
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
            return Or(true)
        else:
            return Or(items)
