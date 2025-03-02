import re
from z3 import *
from ConformantPlanning.Z3_string_constraints import StringConstraints


class sampleGenerator:
    def __init__(self, problem, candidate_plan, action_map, contexts=None):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts # 只有warm starting才用得着context，普通的为None
        self.constraint_object = None
        self.constraint_list = list()
        self.solver = Solver()

    def generate_z3_constraint(self):
        self.constraint_list = self.generate_z3_string_constraints()


    # def generate_z3_object_constraints(self):
    #     self.constraint_object = ObjectConstrains(self.problem, self.candidate_plan, self.action_map, self.contexts)
    #     if self.candidate_plan is not None:
    #         self.constraint_object.regression(self.problem, self.candidate_plan, self.action_map)
    #         self.constraint_object.add_regression_statements()
    #     self.constraint_object.add_precondition_statements()
    #     self.constraint_object.add_initial_statements()
    #     self.constraint_object.add_other_statements()
    #     return self.constraint_object.get_constraints_list()

    def generate_z3_string_constraints(self):
        self.constraint_object = StringConstraints(self.problem, self.candidate_plan, self.action_map, self.contexts)
        regression_assert = ''
        if self.candidate_plan is not None:
            self.constraint_object.regression(self.problem, self.candidate_plan, self.action_map)
            regression_assert = self.constraint_object.get_regression_assert()
        precondition_assert = self.constraint_object.get_precondition_assert()
        initial_assert = self.constraint_object.get_initial_assert()
        declare_assert = self.constraint_object.get_other_assert()
        constraint_string = [declare_assert, regression_assert, precondition_assert, initial_assert]
        return constraint_string


    def compute_single_counter_example(self):
        self.generate_z3_constraint()
        self.solver.from_string(' '.join(self.constraint_list))
        return self.call_SMT_solver()

    def call_SMT_solver(self):
        if self.solver.check() == sat:
            model = self.solver.model()
            return self.extract_counter_example_from_string(model)

    # def extract_counter_example_from_object(self, model):
    #     counter_example = set()
    #     model = model.sexpr()
    #     model = model.strip()
    #     pattern = '\(define-fun (.*) \(\) Bool\n  (.*)\)'
    #     results = re.findall(pattern, model)
    #     for item in results:
    #         if item[0].endswith('-0') and item[1] == 'true':
    #             counter_example.add(self.constraint_object.predicates_to_atom[item[0]])
    #     return counter_example

    def extract_counter_example_from_string(self, model):
        counter_example = set()
        model = model.sexpr()
        model = model.strip()
        pattern = '\(define-fun (.*) \(\) Bool\n  (.*)\)'
        results = re.findall(pattern, model)
        for item in results:
            if item[0].endswith('-0') and item[1] == 'true':
                counter_example.add(self.constraint_object.declared_predicate[item[0]])
        return counter_example


    def dump_smt_statements(self):
        print(self.solver.sexpr())
