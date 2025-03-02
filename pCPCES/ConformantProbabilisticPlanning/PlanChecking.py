from pCPCES.translate.instantiate import explore_probabilistic
from pCPCES.translate.pddl_parser.pddl_file import open
from pCPCES.ConformantProbabilisticPlanning.PlanCheckingTagGenerator import PlanChechingTagGenerator
from pCPCES.Methods.context import Context
from pCPCES.ConformantProbabilisticPlanning.TagGenerator import TagGenerator
from pCPCES.ConformantProbabilisticPlanning.AllProjectedProblems import AllProjectedProblems



class PlanChecking:
    def __init__(self, plan, domain, instance, type='conformant_probabilistic_planning'):
        self.plan = plan
        self.domain = domain
        self.instance = instance
        self.actions = self.get_actions()


    def get_actions(self):
        self.problem = open(self.domain, self.instance, type='conformant_probabilistic_planning')
        temp = self.problem.init
        self.problem.init = self.problem.all_possible_initial
        relaxed_reachable, atoms, actions, axioms, reachable_action = explore_probabilistic(self.problem)
        self.problem.init = temp
        self.contexts = Context(atoms, actions, self.problem.goal,
                           self.problem.all_possible_initial - self.problem.initial_true - self.problem.initial_false)
        self.action_map = self.get_action_map(actions, dict())
        self.get_satisfied_tag_probability()

    def get_action_map(self, actions, result):
        for action in actions:
            result[action.name] = action
        return result

    def get_satisfied_tag_probability(self):
        all_projected_problems = AllProjectedProblems(self.problem, self.contexts)
        probabilistic_tag_generator = TagGenerator(self.problem, self.plan, self.action_map,
                                                   self.contexts)
        # 找到所有tag
        probabilistic_tag_generator.find_all_tags()
        st_generator = PlanChechingTagGenerator(self.problem, self.plan, self.action_map, self.contexts, probabilistic_tag_generator,
                                           all_projected_problems.all_projected_problems)
        probability = st_generator.find_satisfied_tags(threshold=self.problem.threshold)
        print('problem threshold', self.problem.threshold)
        print('satisfied tag probability', probability)
        if probability >= self.problem.threshold:
            print('plan is valid')
        else:
            print('plan is INVALID')
