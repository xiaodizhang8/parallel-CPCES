from pCPCES.translate.pddl.axioms import Axiom
from pCPCES.translate.pddl.predicates import Predicate


class Task:
    def __init__(self, domain_name, task_name, requirements,
                 types, objects, predicates, functions, init, all_possible_initial, initial_true, initial_false, goal,
                 actions, axioms, use_metric, unknown_init_group=None, disjunction_inits=None, constants=None, unknown_initial=None):
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
        self.goal = goal
        self.actions = actions
        self.axioms = axioms
        self.axiom_counter = 0
        self.use_min_cost_metric = use_metric
        self.unknown_init_group = unknown_init_group
        self.disjunction_inits = disjunction_inits
        self.constants = constants
        self.unknown_initial = unknown_initial

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
        print("Unknown Init Groups")
        for unknown_group in self.unknown_init_group:
            print("  One Of")
            for fact in unknown_group:
                print("    %s" % fact)
        print("Disjunction Init Groups")
        for disjunction_group in self.disjunction_inits:
            print("  Or")
            for fact in disjunction_group.parts:
                print("    %s" % fact)
        print("Goal:")
        self.goal.dump()
        print("Actions:")
        for action in self.actions:
            action.dump()
        if self.axioms:
            print("Axioms:")
            for axiom in self.axioms:
                axiom.dump()

class Requirements:
    def __init__(self, requirements):
        self.requirements = requirements
        for req in requirements:
            assert req in (
              ":strips", ":adl", ":typing", ":negation", ":equality",
              ":negative-preconditions", ":disjunctive-preconditions",
              ":existential-preconditions", ":universal-preconditions",
              ":quantified-preconditions", ":conditional-effects",
              ":derived-predicates", ":action-costs"), req
    def __str__(self):
        return ", ".join(self.requirements)
