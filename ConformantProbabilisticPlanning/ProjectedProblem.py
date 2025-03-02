
class ProjectedProblem:
    def __init__(self, constant_init, initial_probability_groups, goal, precondition, effect, problem_index):
        self.constant_init = constant_init
        self.initial_probability_groups = initial_probability_groups
        self.goal = goal
        self.precondition = precondition
        self.effect = effect
        self.problem_index = problem_index