from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.translate.pddl.conditions import Disjunction

class MergingContextTree:
    def __init__(self, fact, successors):
        self.fact = fact
        self.successors = successors

class MergingContext:
    def __init__(self, atoms, actions, goal, unknown_init):
        self.atoms = atoms
        self.actions = actions
        self.goal = goal
        self.contexts = list()
        self.formated_contexts = list()
        self.unknown_init = unknown_init
        self.subgoals = self.compute_subgoals()
        self.context_graph = self.compute_context_graph()
        self.compute_contexts()
        self.all_predicate_name_in_contexts = self.get_all_predicate_name_in_contexts()
        self.all_predicates_in_contexts = self.get_all_predicates_in_contexts()

    def compute_subgoals(self):
        res = set()
        if isinstance(self.goal, Conjunction) or isinstance(self.goal, Disjunction):
            for predicate in self.goal.parts:
                res.add(predicate)
        else:
            res.add(self.goal)
        for action in self.actions:
            for predicate in action.all_preconditions:
                res.add(predicate)
        return res

    def generate_condition_set(self, conditional_effect, add, result):
        conditions = conditional_effect[0]
        if add:
            effect = conditional_effect[1]
        else:
            effect = conditional_effect[1].negate()
        if len(conditions) != 0:
            condition_set = set()
            for condition in conditions:
                if isinstance(condition, NegatedAtom):
                    condition_set.add(condition.negate())
                else:
                    condition_set.add(condition)
            if len(condition_set) != 0:
                if effect not in result.keys():
                    result[effect] = condition_set
                else:
                    result[effect] = result[effect].union(condition_set)
        return result

    def compute_effect_condition_pair(self):
        result = dict()
        for action in self.actions:
            all_effects = action.effects_with_delete
            for effect in all_effects:
                if isinstance(effect[1], Atom):
                    result = self.generate_condition_set(effect, True, result)
                else:
                    result = self.generate_condition_set(effect, False, result)
        return result

    def compute_context_graph(self):
        effect_condition_pair = self.compute_effect_condition_pair()
        graph = dict()
        for fact in self.subgoals:
            queue = list()
            closed = set()
            if isinstance(fact, NegatedAtom):
                queue.append((fact.negate(), None))
            else:
                queue.append((fact, None))
            while len(queue) != 0:
                next = queue[0]
                closed.add(next)
                queue.remove(next)
                if next[1] is not None:
                    if next[1] not in graph.keys():
                        graph[next[1]] = set()
                    graph[next[1]].add(next[0])
                if next[0] in effect_condition_pair.keys():
                    successors = effect_condition_pair[next[0]]
                    for successor in successors:
                        if (successor, next[0]) not in closed:
                            queue.append((successor, next[0]))
        return graph

    def compute_contexts(self):
        effect_condition_pair = self.compute_effect_condition_pair()
        atom_MergingNode_map = dict()
        for fact in self.subgoals:
            dependency = set()
            formated_dependency = set()
            queue = list()
            closed = set()
            if isinstance(fact, NegatedAtom):
                merging_context_tree = MergingContextTree(fact.negate(), set())
                atom_MergingNode_map[fact.negate()] = merging_context_tree
            else:
                merging_context_tree = MergingContextTree(fact, set())
                atom_MergingNode_map[fact] = merging_context_tree
            queue.append(merging_context_tree)
            while len(queue) != 0:
                next = queue[0]
                closed.add(next.fact)
                queue.remove(next)
                next_fact = next.fact
                dependency.add(next_fact)
                formated_dependency.add(next_fact.get_formated_expression())
                if next_fact in effect_condition_pair.keys():
                    successors = self.context_graph[next_fact]
                    for successor in successors:
                        if successor not in closed:
                            if successor in atom_MergingNode_map.keys():
                                new_merging_context_tree = atom_MergingNode_map[successor]
                                next.successors.add(new_merging_context_tree)
                            else:
                                new_merging_context_tree = MergingContextTree(successor, set())
                                atom_MergingNode_map[successor] = new_merging_context_tree
                                next.successors.add(new_merging_context_tree)
                            queue.append(new_merging_context_tree)
            # 去掉一些known的predicate。这些predicate必须在树的最下面的几层，且必须全部在initial state时不属于unknown
            queue2 = list()
            closed2 = set()
            queue2.append(merging_context_tree)
            while len(queue2) != 0:
                current_node = queue2[0]
                queue2.remove(current_node)
                closed2.add(current_node)
                delete_result = self.find_delete_predicates(current_node)
                if delete_result is None:
                    successors = current_node.successors
                    for successor in successors:
                        if successor not in closed2:
                            queue2.append(successor)
                else:
                    for delete_fact in delete_result:
                        if delete_fact in dependency:
                            #TODO: 这个if需要去掉吗？
                            dependency.remove(delete_fact)
            if len(dependency) != 0 and dependency not in self.contexts:
                removed_dependency = []
                for i in self.contexts:
                    if i & dependency == i:
                        removed_dependency.append(i)
                # 如果context1是{a,b},{a,c}这些可以合并
                for i in self.contexts:
                    if len(i & dependency) > 0:
                        removed_dependency.append(i)
                        dependency = dependency | i
                for i in removed_dependency:
                    self.contexts.remove(i)
                self.contexts.append(dependency)
                self.formated_contexts.append(formated_dependency)
            # if len(dependency) != 0 and dependency not in self.contexts:
            #     is_subset = False
            #     for context in self.contexts:
            #         if dependency.issubset(context) or context.issubset(dependency):
            #             is_subset = True
            #     if not is_subset:
            #         self.contexts.append(dependency)
            #         self.formated_contexts.append(formated_dependency)

    def find_delete_predicates(self, node):
        res = set()
        queue = list()
        closed = set()
        queue.append(node)
        while len(queue) != 0:
            current_node = queue[0]
            queue.remove(current_node)
            closed.add(current_node)
            if current_node.fact in self.unknown_init:
                return None
            else:
                res.add(current_node.fact)
                successors = current_node.successors
                for successor in successors:
                    if successor not in closed:
                        queue.append(successor)
        return res

    def get_contexts(self):
        return self.contexts

    def get_formated_contexts(self):
        return self.formated_contexts

    def get_all_predicates_in_contexts(self):
        res = set()
        for context in self.contexts:
            for predicate in context:
                res.add(str(predicate))
        return res

    def get_all_predicate_name_in_contexts(self):
        res = set()
        for context in self.contexts:
            for predicate in context:
                res.add(predicate.predicate)
        return res