#! /usr/bin/env python3


from collections import deque, defaultdict
import itertools
import time

from pCPCES.translate import invariants
from pCPCES.translate import timers
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.f_expression import Assign
from pCPCES.translate.pddl.actions import Action

class BalanceChecker:
    def __init__(self, task, reachable_action_params):
        self.predicates_to_add_actions = defaultdict(set)
        self.action_to_heavy_action = {}
        for act in task.actions:
            action = self.add_inequality_preconds(act, reachable_action_params)
            too_heavy_effects = []
            create_heavy_act = False
            heavy_act = action
            for eff in action.effects:
                too_heavy_effects.append(eff)
                if eff.parameters: # universal effect
                    create_heavy_act = True
                    too_heavy_effects.append(eff.copy())
                if not eff.literal.negated:
                    predicate = eff.literal.predicate
                    self.predicates_to_add_actions[predicate].add(action)
            if create_heavy_act:
                heavy_act = Action(action.name, action.parameters,
                                        action.num_external_parameters,
                                        action.precondition, too_heavy_effects,
                                        action.cost)
            # heavy_act: duplicated universal effects and assigned unique names
            # to all quantified variables (implicitly in constructor)
            self.action_to_heavy_action[action] = heavy_act

    def get_threats(self, predicate):
        return self.predicates_to_add_actions.get(predicate, set())

    def get_heavy_action(self, action):
        return self.action_to_heavy_action[action]

    def add_inequality_preconds(self, action, reachable_action_params):
        if reachable_action_params is None or len(action.parameters) < 2:
            return action
        inequal_params = []
        combs = itertools.combinations(range(len(action.parameters)), 2)
        for pos1, pos2 in combs:
            for params in reachable_action_params[action]:
                if params[pos1] == params[pos2]:
                    break
            else:
                inequal_params.append((pos1, pos2))

        if inequal_params:
            precond_parts = [action.precondition]
            for pos1, pos2 in inequal_params:
                param1 = action.parameters[pos1].name
                param2 = action.parameters[pos2].name
                new_cond = NegatedAtom("=", (param1, param2))
                precond_parts.append(new_cond)
            precond = Conjunction(precond_parts).simplified()
            return Action(
                action.name, action.parameters, action.num_external_parameters,
                precond, action.effects, action.cost)
        else:
            return action

def get_fluents(task):
    fluent_names = set()
    for action in task.actions:
        for eff in action.effects:
            fluent_names.add(eff.literal.predicate)
    return [pred for pred in task.predicates if pred.name in fluent_names]

def get_initial_invariants(task):
    for predicate in get_fluents(task):
        all_args = list(range(len(predicate.arguments)))
        for omitted_arg in [-1] + all_args:
            order = [i for i in all_args if i != omitted_arg]
            part = invariants.InvariantPart(predicate.name, order, omitted_arg)
            yield invariants.Invariant((part,))

def find_invariants(task, reachable_action_params, options):
    limit = options["invariant-generation-max-candidates"]
    candidates = deque(itertools.islice(get_initial_invariants(task), 0, limit))
    # print(len(candidates), "initial candidates")
    seen_candidates = set(candidates)

    balance_checker = BalanceChecker(task, reachable_action_params)

    def enqueue_func(invariant):
        if len(seen_candidates) < limit and invariant not in seen_candidates:
            candidates.append(invariant)
            seen_candidates.add(invariant)

    start_time = time.process_time()
    while candidates:
        candidate = candidates.popleft()
        if time.process_time() - start_time > options["invariant-generation-max-time"]:
            print("Time limit reached, aborting invariant generation")
            return
        if candidate.check_balance(balance_checker, enqueue_func):
            yield candidate

def useful_groups(invariants, initial_facts):
    predicate_to_invariants = defaultdict(list)
    for invariant in invariants:
        for predicate in invariant.predicates:
            predicate_to_invariants[predicate].append(invariant)

    nonempty_groups = set()
    overcrowded_groups = set()
    for atom in initial_facts:
        if isinstance(atom, Assign):
            continue
        for invariant in predicate_to_invariants.get(atom.predicate, ()):
            group_key = (invariant, tuple(invariant.get_parameters(atom)))
            if group_key not in nonempty_groups:
                nonempty_groups.add(group_key)
            else:
                overcrowded_groups.add(group_key)
    useful_groups = nonempty_groups - overcrowded_groups
    for (invariant, parameters) in useful_groups:
        yield [part.instantiate(parameters) for part in sorted(invariant.parts)]

def get_groups(task, options, reachable_action_params=None):
    with timers.timing("Finding invariants", block=True):
        invariants = sorted(find_invariants(task, reachable_action_params, options))
    with timers.timing("Checking invariant weight"):
        result = list(useful_groups(invariants, task.init))
    return result

if __name__ == "__main__":
    import normalize
    import pddl_parser

    print("Parsing...")
    task = pddl_parser.open()
    print("Normalizing...")
    normalize.normalize(task)
    print("Finding invariants...")
    print("NOTE: not passing in reachable_action_params.")
    print("This means fewer invariants might be found.")
    for invariant in find_invariants(task, None):
        print(invariant)
    print("Finding fact groups...")
    groups = get_groups(task)
    for group in groups:
        print("[%s]" % ", ".join(map(str, group)))
