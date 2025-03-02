from z3 import *
import copy
from pCPCES.ConformantProbabilisticPlanning.Z3StringConstraints import StringConstraints
from pCPCES.ConformantProbabilisticPlanning.TagProbability import TagProbability
from pCPCES.ConformantProbabilisticPlanning.MergedProblems import MergedProblems
import random
from hashlib import sha256


class SampleTagsGenerator:
    def __init__(self, problem, candidate_plan, action_map, contexts, tag_generator, all_projected_problems):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts
        self.tag_generator = tag_generator
        self.all_projected_problems = all_projected_problems
        self.sample_tags = None
        self.number_of_sample_tags = 0
        self.used_projected_problems_for_sample_tags = set()

    def get_hash_code(self, s):
        return sha256(str(s).encode('utf-8')).hexdigest()

    def find_sample_tags(self,  threshold=None):
        return self.find_random_sample_tags(threshold=threshold)

    def find_random_sample_tags(self,  threshold=None):
        '''
        随机抽取sample tags
        :param threshold:
        :return:
        '''
        sample_tags = list()
        final_probability = 0
        for i in range(len(self.all_projected_problems.all_projected_problems)):
            sample_tags.append(None)

        all_tags_in_one_list = copy.deepcopy(self.tag_generator.all_tags_in_one_list)
        random.shuffle(all_tags_in_one_list)
        for tag in all_tags_in_one_list:
            pro_index = self.tag_generator.tag_subproblem_index_map[self.get_hash_code(tag)]
            projected_problem = self.all_projected_problems.all_projected_problems[pro_index]
            constant_problem = self.all_projected_problems.constant_problem
            constraint_object = StringConstraints(self.problem, self.candidate_plan, self.action_map,
                                                  self.contexts, self.tag_generator, projected_problem, constant_problem)
            regression_assert = ''
            if self.candidate_plan is not None:
                constraint_object.regression(self.problem, self.candidate_plan, self.action_map)
                regression_assert = constraint_object.get_regression_assert()
            precondition_assert = constraint_object.get_projected_precondition_assert()
            initial_assert = constraint_object.get_projected_initial_assert() # 不需要initial assert，但是需要initial的declare
            constraint_string = [regression_assert, precondition_assert]
            tag_assert = '(assert (and '
            for item in self.tag_generator.all_true_and_false_tags[pro_index]:
                if item == tag:
                    tag_assert += '(and '
                    for predicate in tag:
                        tag_assert += constraint_object.to_smt(predicate, 0) + ' '
                        constraint_object.declared_predicate = predicate.get_predicate(0, constraint_object.declared_predicate)
                    tag_assert += ')'
                else:
                    tag_assert += '(not (and '
                    for predicate in item:
                        tag_assert += constraint_object.to_smt(predicate, 0) + ' '
                        constraint_object.declared_predicate = predicate.get_predicate(0,
                                                                                       constraint_object.declared_predicate)
                    tag_assert += '))'
            tag_assert += '))'
            constraint_string.append(tag_assert)
            declare_assert = constraint_object.get_other_assert()
            constraint_string.insert(0, declare_assert)
            solver = Solver()
            solver.from_string(' '.join(constraint_string))
            if solver.check() != sat:
                if sample_tags[pro_index] is None:
                    sample_tags[pro_index] = [tag]
                else:
                    sample_tags[pro_index].append(tag)
                if threshold is not None:
                    self.number_of_sample_tags += 1
                    self.used_projected_problems_for_sample_tags.add(pro_index)
                    mp_sample = MergedProblems(self.all_projected_problems,
                                        self.used_projected_problems_for_sample_tags, self.problem)
                    mp_sample.merge_problems()
                    tp = TagProbability(self.problem, self.candidate_plan, self.action_map, self.contexts, self.tag_generator,mp_sample)
                    counter_tags_probability = self.compute_multi_tags_probability(sample_tags, tp)
                    if counter_tags_probability > 1:
                        print('概率大于1，有bug！')
                        print('last tag', tag)
                        print('sample tags', sample_tags)
                        print('sample tags probability', counter_tags_probability)
                        exit()
                    final_probability = counter_tags_probability
                    if counter_tags_probability > 1 - threshold:
                        self.sample_tags = sample_tags
                        return sample_tags, counter_tags_probability
        print('没有足够多的sample tag')
        return None, final_probability


    def get_all_tag_probability(self):
        tag_probability_map = dict()
        all_true_and_false_tags = self.tag_generator.all_true_and_false_tags
        for group in all_true_and_false_tags:
            for tag in group:
                tag = list(tag)
                tag.sort()
                tp = TagProbability(self.problem, None, self.action_map, self.contexts, self.tag_generator)
                probability = self.compute_single_tag_probability(tag, tp)
                tag_probability_map[self.get_hash_code(tag)] = probability
        return tag_probability_map

    def is_empty_sample_tags(self, sample_tags):
        for group in sample_tags:
            if group is not None:
                return False
        return True

    def compute_multi_tags_probability(self, sample_tags, tp):
        # 需要先判断sample_tags中是否全为None，即可能没有sample tag。如果没有sample tag直接返回0
        has_sample = False
        for i in sample_tags:
            if i is not None:
                has_sample = True
                break
        if not has_sample:
            return 0
        else:
            temp_sample_tags = copy.deepcopy(sample_tags)
            probability = tp.get_multi_tags_probability(temp_sample_tags)
            return probability

    def compute_satisified_tags_probability(self, sample_tags, tp):
        # 需要先判断sample_tags中是否全为None，即可能没有sample tag。如果没有sample tag直接返回0
        has_sample = False
        for i in sample_tags:
            if i is not None:
                has_sample = True
                break
        if not has_sample:
            return 0
        else:
            temp_sample_tags = copy.deepcopy(sample_tags)
            probability = tp.get_satisfied_tags_probability(temp_sample_tags)
            return probability

    def compute_single_tag_probability(self, tag, tp):
        probability = tp.get_single_tag_probability(tag)
        return probability

    def get_information_from_sample_tags_for_hitting_set(self, tag_index_map):
        res_num = 0
        sample_tag_index = []
        res_used_projected_problems = []
        for i in range(len(self.sample_tags)):
            group = self.sample_tags[i]
            if group is not None:
                for sample_tag in group:
                    sample_tag.sort()
                    index = tag_index_map[self.get_hash_code(sample_tag)]
                    sample_tag_index.append(index)
                    res_num += 1
                    res_used_projected_problems.append(i)
        sample_tag_index.sort()
        return res_num, res_used_projected_problems, sample_tag_index

    def get_information_from_sample_tags(self, sample_tags_history, tag_index_map):
        res_num = 0
        sample_tag_index = []
        res_used_projected_problems = []
        for i in range(len(self.sample_tags)):
            group = self.sample_tags[i]
            if group is not None:
                for sample_tag in group:
                    sample_tag.sort()
                    index = tag_index_map[self.get_hash_code(sample_tag)]
                    sample_tag_index.append(index)
                    res_num += 1
                    res_used_projected_problems.append(i)
        sample_tags_history.append(sample_tag_index)
        return res_num, res_used_projected_problems, sample_tags_history

