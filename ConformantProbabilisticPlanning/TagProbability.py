import os

from pCPCES.ConformantProbabilisticPlanning.NNFConstraints import NNFConstraints
from nnf import And, Or, Var, false, true
import nnf
from hashlib import sha256

class TagProbability:
    def __init__(self, problem, candidate_plan, action_map, contexts, tag_generator, merged_problems=None):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts
        self.tag_generator = tag_generator
        self.merged_problems = merged_problems
        self.constraint_object = NNFConstraints(self.problem, self.candidate_plan, self.action_map,
                                                                self.contexts, self.merged_problems, self.tag_generator)
        self.chance_variables_and_probability = dict() # {'xone-p': 0.4, 'xtwo-p': 0.5, 'yone-p': 0.4, 'ytwo-p': 0.5}
        self.chance_variables = []


    def get_multi_tags_probability(self, sample_tags):
        '''
        计算counter-tag probability, disjunctive
        :param sample_tags:
        :return:
        '''
        self.constraint_object.add_initial_statements()
        self.constraint_object.add_other_statements()
        tag_assert = self.get_multi_tag_assert(sample_tags)
        # self.constraint_object.add_projected_context_statements()
        probability_assert = self.get_probability_assert()
        self.constraint_object.constraints.append(tag_assert)
        self.constraint_object.constraints.append(probability_assert)
        sentence = And(self.constraint_object.constraints)
        sentence.models()
        sentence = sentence.to_CNF()
        # result = nnf.dsharp.compile(sentence, './NNFCompiler/dsharp',extra_args=['-Fgraph', 'a.txt'])
        # result 有两个内容：dnnf, var_labels
        result = nnf.dsharp.compile(sentence, 'pCPCES/NNFCompiler/dsharp')
        if result is false:
            return 0
        return self.parse_dnnf(result[0])

    def get_conjunctive_tags_probability(self, tags):
        '''
        计算hitting set probability, conjunctive
        :param sample_tags:
        :return:
        '''
        self.constraint_object.add_other_statements()
        tag_assert = self.get_conjunctive_tag_assert(tags)
        # self.constraint_object.add_projected_context_statements()
        probability_assert = self.get_probability_assert()
        self.constraint_object.constraints.append(tag_assert)
        self.constraint_object.constraints.append(probability_assert)
        sentence = And(self.constraint_object.constraints)
        sentence.models()
        sentence = sentence.to_CNF()
        # result = nnf.dsharp.compile(sentence, './NNFCompiler/dsharp',extra_args=['-Fgraph', 'a.txt'])
        # result 有两个内容：dnnf, var_labels
        result = nnf.dsharp.compile(sentence, './NNFCompiler/dsharp')
        if result is false:
            return 0
        return self.parse_dnnf(result[0])

    def get_satisfied_tags_probability(self, satisfied_tags):
        '''
        phi and (tag1) and (tag2)...
        :param sample_tags:
        :return:
        '''
        # self.constraint_object.add_projected_initial_statements()
        self.constraint_object.add_other_statements()
        # self.constraint_object.add_projected_context_statements()
        tag_assert = self.get_satisfied_tag_assert(satisfied_tags)
        probability_assert = self.get_probability_assert()
        self.constraint_object.constraints.append(tag_assert)
        self.constraint_object.constraints.append(probability_assert)
        sentence = And(self.constraint_object.constraints)
        sentence.models()
        sentence = sentence.to_CNF()
        # result = nnf.dsharp.compile(sentence, './NNFCompiler/dsharp',extra_args=['-Fgraph', 'a.txt'])
        # result 有两个内容：dnnf, var_labels
        result = nnf.dsharp.compile(sentence, './NNFCompiler/dsharp')
        if result is false:
            return 0
        return self.parse_dnnf(result[0])

    # def get_single_tag_probability(self, tag):
    #     self.constraint_object.add_initial_statements()
    #     self.constraint_object.add_other_statements()
    #     tag_assert = self.get_single_tag_assert(tag)
    #     probability_assert = self.get_probability_assert()
    #     self.constraint_object.constraints.append(tag_assert)
    #     self.constraint_object.constraints.append(probability_assert)
    #     sentence = And(self.constraint_object.constraints)
    #     sentence = sentence.to_CNF()
    #     # result 有两个内容：dnnf, var_labels
    #     result = nnf.dsharp.compile(sentence, './NNFCompiler/dsharp')
    #     if result is false:
    #         return 0
    #     return self.parse_dnnf(result[0])

    def get_hash_code(self, s):
        return sha256(str(s).encode('utf-8')).hexdigest()

    def get_multi_tag_assert(self, sample_tags):
        items = set()
        sample_tag_items = set()
        not_sample_items = set()
        for tag_group in sample_tags:
            if tag_group is not None:
                for tag in tag_group:
                    predicate_set = set()
                    if tag in self.tag_generator.all_tags_in_one_list:
                        for predicate in tag:
                            predicate_set.add(self.constraint_object.to_smt(predicate, 0))
                        sample_tag_items.add(And(predicate_set))
                    else:
                        for predicate in tag:
                            predicate_set.add(self.constraint_object.to_smt(predicate.negate(), 0))
                        not_sample_items.add(Or(predicate_set))
        items.add(Or(sample_tag_items))
        items.add(And(not_sample_items))
        return And(items)

    def get_conjunctive_tag_assert(self, sample_tags):
        items = set()
        sample_tag_items = set()
        not_sample_items = set()
        for tag_group in sample_tags:
            if tag_group is not None:
                for tag in tag_group:
                    predicate_set = set()
                    if tag in self.tag_generator.all_tags_in_one_list:
                        for predicate in tag:
                            predicate_set.add(self.constraint_object.to_smt(predicate, 0))
                        sample_tag_items.add(And(predicate_set))
                    else:
                        for predicate in tag:
                            predicate_set.add(self.constraint_object.to_smt(predicate.negate(), 0))
                        not_sample_items.add(Or(predicate_set))
        items.add(And(sample_tag_items))
        items.add(And(not_sample_items))
        return And(items)


    def get_satisfied_tag_assert(self, satisfied_tags):
        items = set()
        for tag_group in satisfied_tags:
            satisfied_tag_items = set()
            not_satisfied_items = set()
            if tag_group is not None:
                for tag in tag_group:
                    predicate_set = set()
                    if tag in self.tag_generator.all_tags_in_one_list:
                        for predicate in tag:
                            predicate_set.add(self.constraint_object.to_smt(predicate, 0))
                        satisfied_tag_items.add(And(predicate_set))
                    else:
                        for predicate in tag:
                            predicate_set.add(self.constraint_object.to_smt(predicate.negate(), 0))
                        not_satisfied_items.add(Or(predicate_set))
            items.add(Or(satisfied_tag_items))
            items.add(And(not_satisfied_items))
        return And(items)

    def get_contexts_statements(self):
        items = set()
        for group in self.tag_generator.all_true_and_false_tags:
            tag_items = set()
            for tag in group:
                predicate_items = set()
                for predicate in tag:
                    predicate_items.add(self.constraint_object.to_smt(predicate, 0))
                tag_items.add(And(predicate_items))
            items.add(Or(tag_items))
        context_assert = And(items)
        return context_assert


    def get_single_tag_assert(self, tag):
        items = set()
        for predicate in tag:
            items.add(self.constraint_object.to_smt(predicate, 0))
        tag_assert = And(items)
        return tag_assert

    def get_probability_assert(self):
        '''
        这个地方，概率不是原始概率。比如有x1,x2,x3三个fact，概率分别为a,b,c，那么x1对应a，x2对应(not a) and b, x3对应(not a) and (not b)
        那么概率就要进行修改，因为c没有了。b = x2/(not a), c = x3/(not a * not b)
        :return:
        '''
        # probability_assert = ''
        items = set()
        initial_probability_groups = self.problem.initial_probability_groups
        for probabilities in initial_probability_groups:
            predicates = list(probabilities.keys())
            positive_probability_vars = list()
            negative_probability_vars = list()
            group_variables = []
            computed_chance_variables = []
            for index in range(len(predicates)):
                if index != len(predicates) - 1:
                    predicate = predicates[index]
                    probability = probabilities[predicate]
                    name = predicate.predicate + ''.join(predicate.args) + '-p'
                    denominator = 1
                    for i in range(index):
                        denominator *= (1 - self.chance_variables_and_probability[computed_chance_variables[i]])
                    self.chance_variables_and_probability[name] = probability / denominator
                    computed_chance_variables.append(name)
                    name = Var(name)
                    group_variables.append(name)
                    negative_probability_statement = Or({Or(positive_probability_vars), ~name})
                    positive_probability_statement = And({And(negative_probability_vars), name})
                    items.add(Or({self.constraint_object.to_smt(predicate, 0), negative_probability_statement}))
                    items.add(Or({~self.constraint_object.to_smt(predicate, 0), positive_probability_statement}))
                    positive_probability_vars.append(name)
                    negative_probability_vars.append(~name)
                else:
                    predicate = predicates[index]
                    negative_probability_statement = Or(positive_probability_vars)
                    positive_probability_statement = And(negative_probability_vars)
                    items.add(Or({self.constraint_object.to_smt(predicate, 0), negative_probability_statement}))
                    items.add(Or({~self.constraint_object.to_smt(predicate, 0), positive_probability_statement}))
            self.chance_variables.append(group_variables)
        probability_assert = And(items)
        return probability_assert



    def parse_dnnf(self, dnnf):
        probability = None
        if isinstance(dnnf, Or):
            probability = 0
            for child_node in dnnf.children:
                child_probability = self.parse_or(child_node)
                if child_probability is not None:
                    probability += child_probability
        elif isinstance(dnnf, And):
            probability = 1
            for child_node in dnnf.children:
                child_probability = self.parse_and(child_node)
                if child_probability is not None:
                    probability *= child_probability
        return round(probability, 4)

    def parse_or(self, branch):
        probability = None
        if isinstance(branch, Or):
            probability = 0
            for child_node in branch.children:
                child_probability = self.parse_or(child_node)
                if child_probability is not None:
                    probability = probability + child_probability
        elif isinstance(branch, And):
            probability = 1
            for child_node in branch.children:
                child_probability = self.parse_and(child_node)
                if child_probability is not None:
                    probability = probability * child_probability
        elif isinstance(branch, Var):
            probability = self.parse_var(branch)
        if probability is not None:
            return probability



    def parse_and(self, branch):
        probability = None
        if isinstance(branch, Or):
            probability = 0
            for child_node in branch.children:
                child_probability = self.parse_or(child_node)
                if child_probability is not None:
                    probability = probability + child_probability
        elif isinstance(branch, And):
            probability = 1
            for child_node in branch.children:
                child_probability = self.parse_and(child_node)
                if child_probability is not None:
                    probability = probability * child_probability
        elif isinstance(branch, Var):
            probability = self.parse_var(branch)
        if probability is not None:
            return probability

    def parse_var(self, var):
        name = var.name
        bool = var.true
        if bool and name in self.chance_variables_and_probability.keys():
            return round(self.chance_variables_and_probability[name],8)
        if not bool and name in self.chance_variables_and_probability.keys():
            return round(1 - self.chance_variables_and_probability[name],8)

if __name__ == 'main':
    x1, x2, x3, y1, y2, y3, A, B, C, D = Var('x1'), Var('x2'), Var('x3'), Var('y1'), Var('y2'), Var('y3'), Var('A'), Var('B'), Var('C'), Var('D')
    sentence = []
    sentence.append(Or({x1, ~A}))
    sentence.append(Or({x2, Or({A, ~B})}))
    sentence.append(Or({x3, Or({A, B})}))
    sentence.append(Or({~x1, A}))
    sentence.append(Or({~x2, And({~A, B})}))
    sentence.append(Or({~x3, And({~A, ~B})}))
    sentence.append(Or({x1, x2, x3}))
    sentence.append(Or({~x1, ~x2}))
    sentence.append(Or({~x1, ~x3}))
    sentence.append(Or({~x3, ~x2}))

    sentence.append(Or({y1, ~C}))
    sentence.append(Or({y2, Or({C, ~D})}))
    sentence.append(Or({y3, Or({C, D})}))
    sentence.append(Or({~y1, C}))
    sentence.append(Or({~y2, And({~C, D})}))
    sentence.append(Or({~y3, And({~C, ~D})}))
    sentence.append(Or({y1, y2, y3}))
    sentence.append(Or({~y1, ~y2}))
    sentence.append(Or({~y1, ~y3}))
    sentence.append(Or({~y3, ~y2}))

    sentence.append(Or({And({~x1, ~x2, x3}), And({y1, ~y2, ~y3})}))

    final = And(sentence)
    cnf = final.to_CNF()
    dnnf, var_labels = nnf.dsharp.compile(cnf, '/Users/xiaodizhang/PycharmProjects/probability-CPCES/NNFCompiler/dsharp',extra_args=['-Fgraph', '/Users/xiaodizhang/PycharmProjects/probability-CPCES/b.txt'])
    print(var_labels)