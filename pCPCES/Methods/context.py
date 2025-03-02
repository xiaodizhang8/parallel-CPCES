from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.translate.pddl.conditions import Disjunction

class Context:

    def __init__(self, atoms, actions, goal, unknown_init, multiple=False):
        self.atoms = atoms
        self.actions = actions
        self.goal = goal
        self.contexts = list()
        self.formated_contexts = list()  # 这里contexts使用list是为了固定每个context的位置，之后计算tag时可直接根据context的位置确定tag的位置
        self.distance_contexts = list()  # 计算context中一个predicate到其他predicate最远的距离
        self.highest_distance_contexts = dict()
        self.unknown_init = unknown_init
        self.subgoals = self.compute_subgoals()
        self.context_graph = None
        self.compute_contexts()
        if multiple:
            self.context_graph = self.compute_context_graph()
            self.compute_distance_contexts()
            # print('distance contexts')
            # print(self.distance_contexts)
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
        for fact in self.subgoals:
            context = set()
            formated_context = set()
            queue = list()
            closed = set()
            if isinstance(fact, NegatedAtom):
                queue.append(fact.negate())
            else:
                queue.append(fact)
            while len(queue) != 0:
                next = queue[0]
                closed.add(next)
                queue.remove(next)
                context.add(next)
                formated_context.add(next.get_formated_expression())
                if next in effect_condition_pair.keys():
                    successors = effect_condition_pair[next]
                    for successor in successors:
                        if successor not in closed:
                            queue.append(successor)
            if len(context & self.unknown_init) != 0 and context not in self.contexts:
                removed_contexts = []
                for i in self.contexts:
                    if i & context == i and i not in removed_contexts:
                        removed_contexts.append(i)
                # 如果context1是{a,b},{a,c}这些可以合并
                for i in self.contexts:
                    if len(i & context) > 0:
                        if i not in removed_contexts:
                            removed_contexts.append(i)
                        context = context | i
                for i in removed_contexts:
                    self.contexts.remove(i)
                self.contexts.append(context)
                self.formated_contexts.append(formated_context)

    # def compute_contexts(self):
    #     for fact in self.subgoals:
    #         context = set()
    #         formated_context = set()
    #         queue = list()
    #         closed = set()
    #         if isinstance(fact, NegatedAtom):
    #             queue.append(fact.negate())
    #         else:
    #             queue.append(fact)
    #         while len(queue) != 0:
    #             next = queue[0]
    #             closed.add(next)
    #             queue.remove(next)
    #             context.add(next)
    #             formated_context.add(next.get_formated_expression())
    #             if next in self.context_graph.keys():
    #                 successors = self.context_graph[next]
    #                 for successor in successors:
    #                     if successor not in closed:
    #                         queue.append(successor)
    #         if len(context & self.unknown_init) != 0 and context not in self.contexts:
    #             self.contexts.append(context)
    #             self.formated_contexts.append(formated_context)

    def compute_distance_contexts(self):
        for context in self.contexts:
            distance_context = dict()
            for predicate in context:
                max_distance = 0
                queue = list()
                closed = set()
                queue.append((predicate, 0))
                closed.add(predicate)
                while len(queue) != 0:
                    next = queue[0]
                    queue.remove(next)
                    if next[1] > max_distance:
                        max_distance = next[1]
                    if next[0] in self.context_graph.keys():
                        for successor in self.context_graph[next[0]]:
                            if successor not in closed:
                                queue.append((successor, next[1] + 1))
                                closed.add(successor)
                distance_context[predicate] = max_distance
                if predicate not in self.highest_distance_contexts.keys():
                    self.highest_distance_contexts[predicate] = max_distance
                else:
                    if max_distance > self.highest_distance_contexts[predicate]:
                        self.highest_distance_contexts[predicate] = max_distance
            self.distance_contexts.append(distance_context)


    def get_contexts(self):
        return self.contexts

    def get_formated_contexts(self):
        return self.formated_contexts

    def get_all_predicate_name_in_contexts(self):
        res = set()
        for context in self.contexts:
            for predicate in context:
                res.add(predicate.predicate)
        return res

    def get_all_predicates_in_contexts(self):
        res = set()
        for context in self.contexts:
            for predicate in context:
                res.add(predicate)
        return res

    def get_predicate_name_in_contexts(self):
        res = []
        for context in self.contexts:
            context_group = set()
            for predicate in context:
                context_group.add(predicate.predicate)
            res.append(context_group)
        return res