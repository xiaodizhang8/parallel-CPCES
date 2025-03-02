from pCPCES.translate.pddl.conditions import Truth
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.translate.pddl.conditions import Disjunction
from pCPCES.ConformantProbabilisticPlanning.ProjectedProblem import ProjectedProblem

class AllProjectedProblems:
    def __init__(self, problem, contexts):
        self.problem = problem
        self.contexts = contexts
        self.all_projected_problems = self.get_all_projected_problems()
        self.constant_problem = self.get_constant_problem()

    def get_all_projected_problems(self):
        res_init = []
        res_initial_probability_groups = []
        res_goal = []
        res_precondition = []
        res_effect = []
        context_names = self.contexts.get_predicate_name_in_contexts()
        contexts = self.contexts.contexts
        for context in contexts:
            # 处理initial为true的
            init_set = set()
            for init in self.problem.init:
                if init in context:
                    init_set.add(init)
            res_init.append(init_set)
            # 处理initial有概率的
            initial_probability_list = []
            for group in self.problem.initial_probability_groups:
                res_group = dict()
                for fact, probability in group.items():
                    if fact in context:
                        res_group[fact] = probability
                if len(res_group) != 0:
                    initial_probability_list.append(res_group)
            res_initial_probability_groups.append(initial_probability_list)
            # 处理goal
            goal_set = set()
            if isinstance(self.problem.goal, Atom) or isinstance(self.problem.goal, NegatedAtom):
                if self.problem.goal in context or self.problem.goal.negate() in context:
                    goal_set.add(self.problem.goal)
            else:
                for goal in self.problem.goal.parts:
                    if goal in context or goal.negate() in context:
                        goal_set.add(goal)
            res_goal.append(goal_set)
        for names in context_names:
            action_precondition = dict()
            for action in self.problem.actions:
                if action.name not in action_precondition.keys():
                    action_precondition[action.name] = set()
                precondition = action.precondition
                if isinstance(precondition, Atom) or isinstance(precondition, NegatedAtom):
                    if precondition.predicate in names and precondition not in action_precondition[action.name]:
                        action_precondition[action.name].add(precondition)
                else:
                    for item in precondition.parts:
                        if item.predicate in names and item not in action_precondition[action.name]:
                            action_precondition[action.name].add(item)
            res_precondition.append(action_precondition)
            # 处理effect
            action_effect = dict()
            for action in self.problem.actions:
                if action.name not in action_effect.keys():
                    action_effect[action.name] = []
                conditional_effects = action.effects
                for conditional_effect in conditional_effects:
                    condition = conditional_effect.condition
                    effect = conditional_effect.literal
                    if isinstance(condition, Truth):
                        if effect.predicate in names:
                            action_effect[action.name].append(conditional_effect)
                    else:
                        if effect.predicate in names:
                            action_effect[action.name].append(conditional_effect)
            res_effect.append(action_effect)
        assert len(contexts) == len(res_init) == len(res_initial_probability_groups) == len(res_goal) == len(res_precondition) == len(res_effect)
        projected_problems = []
        for i in range(len(contexts)):
            projected_problem = ProjectedProblem(res_init[i], res_initial_probability_groups[i], res_goal[i], res_precondition[i], res_effect[i], i)
            projected_problems.append(projected_problem)
        return projected_problems

    def get_constant_problem(self):
        res_constant_init = set()
        res_precondition = dict()
        res_effect = dict()
        context_names = self.contexts.get_predicate_name_in_contexts()
        contexts = self.contexts.contexts
        # context_predicates_set = set()
        context_names_set = set()
        # for context in contexts:
        #     print(context)
        #     for predicate in context:
        #         context_predicates_set.add(predicate)
        for name_group in context_names:
            for name in name_group:
                context_names_set.add(name)
        for init in self.problem.init:
            if init.predicate != '=':
                res_constant_init.add(init)
        # 处理action
        for action in self.problem.actions:
            if action.name not in res_precondition.keys():
                res_precondition[action.name] = set()
            precondition = action.precondition
            if isinstance(precondition, Atom) or isinstance(precondition, NegatedAtom):
                if precondition.predicate not in context_names_set and precondition not in res_precondition[action.name]:
                    res_precondition[action.name].add(precondition)
            else:
                for item in precondition.parts:
                    if item.predicate not in context_names_set and item not in res_precondition[action.name]:
                        res_precondition[action.name].add(item)
        # 处理effect
        for action in self.problem.actions:
            if action.name not in res_effect.keys():
                res_effect[action.name] = []
            conditional_effects = action.effects
            for conditional_effect in conditional_effects:
                condition = conditional_effect.condition
                effect = conditional_effect.literal
                if isinstance(condition, Truth):
                    if effect.predicate not in context_names_set:
                        res_effect[action.name].append(conditional_effect)
                else:
                    if effect.predicate not in context_names_set:
                        res_effect[action.name].append(conditional_effect)
        projected_problem = ProjectedProblem(res_constant_init, None, None, res_precondition, res_effect, None)
        return projected_problem