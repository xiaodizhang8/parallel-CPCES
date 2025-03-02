
import copy


class MergedProblems:
    def __init__(self, all_projected_problems, used_projected_problems, problem):
        self.problem_projection = all_projected_problems
        self.all_projected_problems = all_projected_problems.all_projected_problems
        self.constant_problem = all_projected_problems.constant_problem
        self.used_projected_problems = used_projected_problems
        self.problem = problem
        self.constant_init = None
        self.initial_probability_groups = None
        self.goal = None
        self.precondition = None
        self.effect = None
        self.add_constant_problem()

    def merge_problems(self):
        assert len(self.used_projected_problems) > 0
        # self.merge_constant_problem(used_projected_problems)
        for projected_problem_index in self.used_projected_problems:
            self.merge_two_projected_problems(projected_problem_index)


    def add_constant_problem(self):
        self.constant_init = self.constant_problem.constant_init
        self.goal = []
        self.initial_probability_groups = []
        self.precondition = dict()
        for action, precondition in self.constant_problem.precondition.items():
            self.precondition[action] = [precondition]
        self.effect = self.constant_problem.effect


    def merge_two_projected_problems(self, projected_problem_index):
        self.constant_init = self.constant_init | self.all_projected_problems[projected_problem_index].constant_init
        self.merged_two_initial_probability_groups(projected_problem_index)
        # self.initial_probability_groups = self.initial_probability_groups + self.all_projected_problems[projected_problem_index].initial_probability_groups
        self.goal.append(self.all_projected_problems[projected_problem_index].goal)
        for action, precondition in self.all_projected_problems[projected_problem_index].precondition.items():
            if precondition not in self.precondition[action]:
                self.precondition[action].append(precondition)
        for action, effect in self.all_projected_problems[projected_problem_index].effect.items():
            if effect not in self.effect[action]:
                merged_effect = effect + self.effect[action]
                self.effect[action] = merged_effect

    def merged_two_initial_probability_groups(self, projected_problem_index):
        new_initial_probability_groups = copy.deepcopy(self.all_projected_problems[projected_problem_index].initial_probability_groups)
        group_need_to_be_added = list()
        for new_group in new_initial_probability_groups:
            if len(self.initial_probability_groups) == 0:
                self.initial_probability_groups.append(new_group)
            else:
                for old_group in self.initial_probability_groups:
                    for all_group in self.problem.initial_probability_groups:
                        merged_keys = set(new_group.keys()) | set(old_group.keys())
                        if set(all_group.keys()) & merged_keys == merged_keys:
                            old_group.update(new_group)
                        else:
                            group_need_to_be_added.append(new_group)
        for group in group_need_to_be_added:
            self.initial_probability_groups.append(group)


