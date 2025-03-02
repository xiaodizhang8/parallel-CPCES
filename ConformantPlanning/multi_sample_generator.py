import re
from z3 import *
from translate.pddl.conditions import Atom
from ConformantPlanning.Z3_object_constraints import ObjectConstrains


class multiSampleGenerator:
    def __init__(self, problem, candidate_plan, action_map, contexts=None):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts # 只有warm starting才用得着context，普通的为None
        self.constraint_object = None
        self.solver = Solver()


    def compute_multiple_counter_examples_for_warm_starting(self):
        unknown_init = set(
            [predicate for group in self.problem.unknown_init_group for predicate in group]) | self.problem.unknown_initial
        all_possible_initial = self.problem.all_possible_initial
        false_predicates = set()
        for distance_context in self.contexts.distance_contexts:
            remove_predicates = set()
            max_distance = 0
            for predicate in distance_context.keys():
                if predicate not in all_possible_initial:  # 比如disposed, holding就属于不在all_possible_initial中
                    remove_predicates.add(predicate)
                else:
                    if predicate in unknown_init and distance_context[predicate] > max_distance:  # 顺便计算context中的最大距离
                        max_distance = distance_context[predicate]
            for predicate, distance in distance_context.items():
                if distance < max_distance and predicate not in remove_predicates:
                    false_predicates.add(predicate)

        predicates_map = dict()  # 普通格式-Atom格式
        for predicate in self.problem.all_possible_initial | self.problem.initial_true | self.problem.initial_false:
            if isinstance(predicate, Atom):
                predicates_map[predicate.get_formated_expression()] = predicate
            else:
                predicates_map[predicate.negate().get_formated_expression()] = predicate.negate()

        self.constraint_object = ObjectConstrains(self.problem, self.candidate_plan, self.action_map, self.contexts)
        self.constraint_object.add_precondition_statements()
        self.constraint_object.add_initial_statements()
        self.constraint_object.add_other_statements()
        self.solver.add(self.constraint_object.constraints)
        for predicate in false_predicates:
            if predicate in unknown_init:
                bool_item = self.constraint_object.to_smt(predicate, 0)
                self.constraint_object.constraints.append(Not(bool_item))

        counter_example = self.call_SMT_solver()
        sample_list = list()
        while counter_example is not None:
            sample_list.append(counter_example)
            for predicate in counter_example:
                if predicates_map[predicate] in unknown_init:
                    bool_item = self.constraint_object.to_smt(predicates_map[predicate], 0)
                    self.solver.push()
                    self.solver.add(Not(bool_item))
            counter_example = self.call_SMT_solver()
        return sample_list



    def call_SMT_solver(self):
        if self.solver.check() == sat:
            model = self.solver.model()
            return self.extract_counter_example(model)
        else:
            return None

    def extract_counter_example(self, model):
        counter_example = set()
        model = model.sexpr()
        model = model.strip()
        pattern = '\(define-fun (.*) \(\) Bool\n  (.*)\)'
        results = re.findall(pattern, model)
        for item in results:
            if item[0].endswith('-0') and item[1] == 'true':
                counter_example.add(self.constraint_object.predicates_to_atom[item[0]])
        return counter_example


    def dump_smt_statements(self):
        print(self.solver.sexpr())
