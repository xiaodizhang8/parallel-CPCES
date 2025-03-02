from pCPCES.translate.pddl.axioms import Axiom
from pCPCES.translate.pddl.predicates import Predicate


class ProbabilisticTask:
    def __init__(self, domain_name, task_name, requirements,
                 types, objects, predicates, functions, init, all_possible_initial, initial_true, initial_false, initial_probability_groups, all_initial_unknown, threshold, goal,
                 actions, axioms, use_metric, disjunction_inits=None, constants=None):
        self.domain_name = domain_name
        self.task_name = task_name
        self.requirements = requirements
        self.types = types
        self.objects = objects
        self.predicates = predicates
        self.functions = functions
        self.init = init
        self.all_possible_initial = all_possible_initial
        self.initial_true = initial_true
        self.initial_false = initial_false
        self.initial_probability_groups = initial_probability_groups
        self.all_initial_unknown = all_initial_unknown
        self.threshold = threshold
        self.goal = goal
        self.actions = actions
        self.axioms = axioms
        self.axiom_counter = 0
        self.use_min_cost_metric = use_metric
        self.disjunction_inits = disjunction_inits
        self.constants = constants

    def add_axiom(self, parameters, condition):
        name = "new-axiom@%d" % self.axiom_counter
        self.axiom_counter += 1
        axiom = Axiom(name, parameters, len(parameters), condition)
        self.predicates.append(Predicate(name, parameters))
        self.axioms.append(axiom)
        return axiom

    def dump(self):
        print("Problem %s: %s [%s]" % (
            self.domain_name, self.task_name, self.requirements))
        print("Types:")
        for type in self.types:
            print("  %s" % type)
        print("Objects:")
        for obj in self.objects:
            print("  %s" % obj)
        if self.constants is not None:
            print("Constants:")
            for cons in self.constants:
                print("  %s" % cons)
        print("Predicates:")
        for pred in self.predicates:
            print("  %s" % pred)
        print("Functions:")
        for func in self.functions:
            print("  %s" % func)
        print("Init:")
        for fact in self.init:
            print("  %s" % fact)
        print("Initial False:")
        for fact in self.initial_false:
            print("  %s" % fact)
        print("Disjunction Init Groups")
        for disjunction_group in self.disjunction_inits:
            print("  Or")
            for fact in disjunction_group.parts:
                print("    %s" % fact)
        print("Probabilistic Initial:")
        for group in self.initial_probability_groups:
            print("  Group")
            for fact, probability in group.items():
                print("    %s: %s" % (fact, probability))
        print("Goal:")
        self.goal.dump()
        print('  Threshold')
        print('    %s' % self.threshold)
        print("Actions:")
        for action in self.actions:
            action.dump()
        if self.axioms:
            print("Axioms:")
            for axiom in self.axioms:
                axiom.dump()
        print('All Possible Initials')
        print(self.all_possible_initial)

