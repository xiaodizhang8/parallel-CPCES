import re
from z3 import *
from pCPCES.ConformantProbabilisticPlanning.Z3StringConstraints import StringConstraints
from hashlib import sha256



class TagGenerator:
    def __init__(self, problem, candidate_plan, action_map, contexts):
        self.problem = problem
        self.candidate_plan = candidate_plan
        self.action_map = action_map
        self.contexts = contexts
        self.tag_index = 0 # 用于给tag编号，初始时为0
        self.all_true_tags = [] # 只记录fact为True的tag，false的不记录
        self.all_true_and_false_tags = [] # 记录fact为True和False的tag
        self.all_true_and_false_tags_by_index = [] #记录fact为True和False的tag的index
        self.all_tags_in_one_list = [] # 不按subproblem分组， 且为True和False的tag
        self.tag_index_map = dict() # 记录每个tag对应的index数字
        self.index_tag_map = dict() # 记录每个index对应的tag
        self.all_index = set() # 记录所有index
        self.tag_subproblem_index_map = dict() # 记录每个tag对应subproblem的index数字
        for i in range(len(self.contexts.contexts)):
            self.all_true_tags.append([])
            self.all_true_and_false_tags.append([])
            self.all_true_and_false_tags_by_index.append([])
        self.constraint_list = list()


    def find_all_tags(self):
        self.constraint_object = StringConstraints(self.problem, self.candidate_plan, self.action_map, self.contexts, self)
        initial_assert = self.constraint_object.get_initial_assert()
        other_assert = self.constraint_object.get_other_assert()
        constraints = [other_assert, initial_assert]
        success = self.call_SMT(constraints)
        if not success:
            print('no tag found')
            exit()
        for pro_index in range(len(self.contexts.contexts)):
            if self.contexts.contexts[pro_index] is None:
                continue
            while True:
                seen_tags = self.all_true_and_false_tags[pro_index]
                if len(seen_tags) == 0:
                    break
                tag_assert = self.get_tag_assert(seen_tags)
                constraints.append(tag_assert)
                success = self.call_SMT(constraints)
                constraints.remove(tag_assert)
                if not success:
                    break
        if len(self.all_true_and_false_tags) > 1: #剔除重复的tag group
            last_group = self.all_true_and_false_tags[-1]
            last_group.sort()
            for tag_group in self.all_true_and_false_tags[:-1]:
                tag_group.sort()
                if tag_group == last_group:
                    self.all_true_and_false_tags[-1] = []
                    break
        # print('all true', self.all_true_tags)
        # print('all', self.all_true_and_false_tags)
        # print('index tag map', self.index_tag_map)




    def get_tag_assert(self, tags):
        res = '(assert (and '
        for tag in tags:
            res += '(not (and '
            for predicate in tag:
                res += self.constraint_object.to_smt(predicate, 0) + ' '
            res +='))'
        res += '))\n'
        return res


    def call_SMT(self, constraint_list):
        solver = Solver()
        solver.from_string(' '.join(constraint_list))
        if solver.check() == sat:
            model = solver.model()
            self.extract_tags(model, self.constraint_object.predicates_to_atom)
            return True
        else:
            return False

    def extract_tags(self, model, predicate_to_atom):
        true_items = set()
        false_items = set()
        model = model.sexpr()
        model = model.strip()
        pattern = '\(define-fun (.*) \(\) Bool\n  (.*)\)'
        results = re.findall(pattern, model)
        for item in results:
            if item[0].endswith('-0') and item[1] == 'true':
                item = item[0]
                item = predicate_to_atom[item]
                if item not in self.problem.initial_true and item.negate() not in self.problem.initial_false:
                    true_items.add(item)
            elif item[0].endswith('-0') and item[1] == 'false':
                item = item[0]
                item = predicate_to_atom[item]
                if item not in self.problem.initial_false and item.negate() not in self.problem.initial_true:
                    false_items.add(item.negate())
        for pro_index in range(len(self.contexts.contexts)):
            if self.contexts.contexts[pro_index] is None:
                continue
            tag_true = []
            tag_all = []
            for item in true_items:
                if item in self.contexts.contexts[pro_index]:
                    tag_true.append(item)
                    tag_all.append(item)
            for item in false_items:
                if item.negate() in self.contexts.contexts[pro_index]:
                    tag_all.append(item)

            tag_true.sort()
            tag_all.sort()
            if len(tag_true) != 0 and tag_true not in self.all_true_tags[pro_index]:
                self.all_true_tags[pro_index].append(tag_true)
            if len(tag_all) != 0 and tag_all not in self.all_true_and_false_tags[pro_index] and tag_all not in self.all_tags_in_one_list:
                self.all_true_and_false_tags[pro_index].append(tag_all)
                self.all_tags_in_one_list.append(tag_all)
                tag_all = list(tag_all)
                tag_all.sort()
                self.tag_index_map[self.get_hash_code(tag_all)] = self.tag_index
                self.index_tag_map[self.tag_index] = tag_all
                self.tag_subproblem_index_map[self.get_hash_code(tag_all)] = pro_index
                self.all_true_and_false_tags_by_index[pro_index].append(self.tag_index)
                self.all_index.add(self.tag_index)
                self.tag_index += 1

    def get_hash_code(self, s):
        return sha256(str(s).encode('utf-8')).hexdigest()


