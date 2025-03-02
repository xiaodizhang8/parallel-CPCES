import re
import subprocess
import itertools
from collections import OrderedDict
from Methods.classical_planning import extract_fd_plan
from translate import pddl_parser
from translate import normalize
from translate import translate
from Methods.classical_planning import write_no_empty_plan_domain_file
from Methods.classical_planning import write_no_empty_plan_instance_file

class FDPlanGenerator:
    def __init__(self, classical_domain_file, classical_instance_file, merging_contexts):
        self.classical_domain_file = classical_domain_file
        self.classical_instance_file = classical_instance_file
        self.merging_contexts = merging_contexts
        self.all_formated_predicates_in_merging_contexts = merging_contexts.get_all_predicates_in_contexts()
        self.predicate_variable_map = OrderedDict()
        self.variable_variable_map = OrderedDict()
        self.variable_predicate_map = OrderedDict()
        self.variable_actual_predicate_map = OrderedDict() # 记录真实的predicate，即不加inter的，用于合并variable
        self.variable_sas_format_predicate_map = OrderedDict() # 记录可用于写入sas的predicate，即有些带有inter，有些可以合并的不带inter
        self.variable_axiom_map = OrderedDict()
        self.start_state = OrderedDict()
        self.goal_state = OrderedDict()
        self.action_axiom_map = OrderedDict()
        self.action = OrderedDict()
        self.rule = OrderedDict()
        self.empty_rule = set()
        self.variable_num = 0 # 每轮更新之后总共的variable数量
        self.new_variable_num = 0 # 每轮新生成的variable数量
        self.total_variables = 0  # 合并前所有sas的variable数量
        self.can_merge_variable = True
        self.options = {
            "generate_relaxed_task": False,
            "use_partial_encoding": True,
            "invariant-generation-max-candidates": 100000,
            "invariant-generation-max-time": 300,
            "add-implied-preconditions": False,
            "filter_unreachable_facts": True,
            "reorder_variables": True,
            "filter_unimportant_vars": True,
            "dump-task": False,
            "layer-strategy": "min"
        }



    def read_sas(self, iteration):
        self.new_variable_num = 0
        self.variable_variable_map = OrderedDict()
        self.duplicated_variable_variable_map = OrderedDict()
        with open('output.sas', 'r') as f:
            lines = f.readlines()
            index = 0
            while (index < len(lines)):
                # 读取variables
                line = lines[index].strip()
                if line == 'begin_variable':
                    self.total_variables += 1
                    var_name = lines[index + 1].strip()
                    var_axiom = lines[index + 2].strip()
                    var_index = re.findall(r'var(.+)', var_name)[0]
                    index = index + 4
                    predicate = lines[index].strip()
                    predicate_args = re.findall(r'\(.+\)', predicate)
                    if len(predicate_args) != 0:
                        predicate_args = '(' + predicate_args[0][1:-1] + ')'
                    else:
                        predicate_args = '()'
                    if predicate_args == '()':
                        new_predicate = predicate.replace(predicate_args, '(inter' + str(iteration) + ')')
                    else:
                        if predicate == 'Atom dummy(val1)':
                            new_predicate = predicate
                        else:
                            new_predicate = predicate.replace(predicate_args,
                                                              '(' + predicate_args.replace('(', '').replace(')',
                                                                                                            '') + ', inter' + str(
                                                                  iteration) + ')')
                    if new_predicate in self.predicate_variable_map.keys():
                        old_var_index = self.predicate_variable_map.get(new_predicate)
                        self.variable_variable_map[int(var_index)] = old_var_index
                    else:
                        old_var_index = self.variable_num + self.new_variable_num
                        self.variable_variable_map[int(var_index)] = old_var_index
                        predicates = list()
                        actual_predicates = list()
                        sas_format_predicates = list()
                        while lines[index].strip() != 'end_variable':
                            predicate = lines[index].strip()
                            predicate_args = re.findall(r'\(.+\)', predicate)
                            if len(predicate_args) != 0:
                                predicate_args = '(' + predicate_args[0][1:-1] + ')'
                            else:
                                predicate_args = '()'
                            if predicate_args == '()':
                                new_predicate = predicate.replace(predicate_args, '(inter' + str(iteration) + ')')
                            else:
                                new_predicate = predicate.replace(predicate_args,
                                                                  '(' + predicate_args.replace('(', '').replace(')',
                                                                                                                '') + ', inter' + str(
                                                                      iteration) + ')')
                            predicates.append(new_predicate)
                            actual_predicates.append(predicate)
                            self.predicate_variable_map[new_predicate] = old_var_index
                            index += 1
                        # 此时其中一个variable的信息已经读取完成，需要检查该variable是否和前面的variable完全一样，并进行合并
                        variable_index, original_predicates = self.check_duplicated_variables(actual_predicates)
                        if variable_index is None or not self.can_merge_variable:
                            self.variable_predicate_map[old_var_index] = predicates
                            self.variable_actual_predicate_map[old_var_index] = actual_predicates
                            self.variable_sas_format_predicate_map[old_var_index] = predicates
                            self.variable_axiom_map[old_var_index] = var_axiom
                            self.new_variable_num += 1
                        else:
                            # 合并variable。如果是多余variable, 移除一些新加的内容
                            self.duplicated_variable_variable_map[int(var_index)] = variable_index
                            self.variable_variable_map.pop(int(var_index))
                            for predicate in predicates:
                                self.predicate_variable_map[predicate] = variable_index
                            self.variable_sas_format_predicate_map[variable_index] = original_predicates
                    continue
                # 读取start states
                if line == 'begin_state':
                    # 检查是否sas和之前一样，仅针对第二轮
                    if iteration == 2 and self.new_variable_num == 0:
                        self.can_merge_variable = False
                        return "Cannot merge variables"
                    index += 1
                    var_index = 0
                    while lines[index].strip() != 'end_state':
                        state = int(lines[index].strip())
                        if var_index in self.variable_variable_map.keys():
                            old_var_index = self.variable_variable_map[var_index]
                            self.start_state[old_var_index] = state
                        index += 1
                        var_index += 1
                    continue
                # 读取goal
                if line == 'begin_goal':
                    index = index + 2
                    while lines[index].strip() != 'end_goal':
                        content = lines[index].strip().split(' ')
                        var_index = int(content[0])
                        state = int(content[1])
                        if var_index in self.variable_variable_map.keys():
                            old_var_index = self.variable_variable_map[var_index]
                            self.goal_state[old_var_index] = state
                        index += 1
                    continue
                # 读取action
                if line == 'begin_operator':
                    action_name = lines[index + 1].strip()
                    index = index + 2
                    if lines[index].strip() != '0':
                        action_axiom = set()
                        index += 1
                        while len(lines[index].strip().split()) != 1:
                            axiom = lines[index].strip().split(' ')
                            var_index = int(axiom[0])
                            axiom_value = int(axiom[1])
                            if var_index in self.variable_variable_map.keys():
                                old_var_index = self.variable_variable_map[var_index]
                                action_axiom.add(str(old_var_index) + ' ' + str(axiom_value))
                            else:
                                action_axiom.add(str(var_index) + ' ' + str(axiom_value))
                            index += 1
                        if action_name in self.action_axiom_map.keys():
                            self.action_axiom_map[action_name] = self.action_axiom_map[action_name] | action_axiom
                        else:
                            self.action_axiom_map[action_name] = action_axiom
                        index -= 1
                    index += 2
                    effects = set()
                    while lines[index].strip() != 'end_operator' and lines[index].strip() != '1':
                        string_builder = ''
                        content = lines[index].strip().split(' ')
                        deleted_var = False
                        for i in range(len(content)):
                            num = int(content[i])
                            if i % 2 == 1 and i != len(content) - 1:
                                if num in self.variable_variable_map.keys():
                                    old_num = self.variable_variable_map[num]
                                    string_builder += str(old_num) + ' '
                                else:
                                    old_num = self.duplicated_variable_variable_map[num]
                                    string_builder += str(old_num) + ' '
                            else:
                                string_builder += str(num) + ' '
                        if len(string_builder[:-1].split(' ')) != 2:
                            effects.add(string_builder[:-1])
                        index += 1
                    if action_name in self.action.keys():
                        self.action[action_name] = self.action[action_name].union(effects)
                    else:
                        self.action[action_name] = effects
                    continue
                # 读取rules
                if line == 'begin_rule':
                    if lines[index + 1].strip() == '0':
                        content = lines[index + 2].strip().split(' ')
                        num = int(content[0])
                        if num in self.variable_variable_map.keys():
                            new_num = self.variable_variable_map[num]
                            self.empty_rule.add(str(new_num) + ' ' + content[1] + ' ' + content[2])
                        index += 4
                    else:
                        index += 2
                        rules = set()
                        while len(lines[index].strip().split(' ')) != 3:
                            string_builder = ''
                            content = lines[index].strip().split(' ')
                            num = int(content[0])
                            if num in self.variable_variable_map.keys():
                                new_num = self.variable_variable_map[num]
                                string_builder += str(new_num) + ' ' + content[1]
                                rules.add(string_builder)
                            index += 1
                        rule_key = lines[index].strip().split(' ')
                        if rule_key[1] == '0' and rule_key[2] == '1':
                            key = int(rule_key[0])
                            if key in self.variable_variable_map.keys():
                                old_key = self.variable_variable_map[key]
                                if str(old_key) + ' ' + rule_key[1] + ' ' + rule_key[2] not in self.rule.keys():
                                    self.rule[str(old_key) + " " + rule_key[1] + " " + rule_key[2]] = rules
                                else:
                                    self.rule[str(old_key) + " " + rule_key[1] + " " + rule_key[2]] = self.rule[
                                                                                                          str(old_key) + " " +
                                                                                                          rule_key[
                                                                                                              1] + " " +
                                                                                                          rule_key[
                                                                                                              2]] | rules
                    continue
                index += 1
            self.variable_num += self.new_variable_num



    def check_duplicated_variables(self, new_actual_predictes):
        # 寻找完全相同的variable
        # 由于每轮都会做筛选，所以只存在两两相同的情况，不存在3个或以上相同的情况
        original_predicates = self.revert_to_original_predicates(new_actual_predictes)
        for variable_index, actual_predicates in self.variable_actual_predicate_map.items():
            if actual_predicates == new_actual_predictes:
                for predicate in new_actual_predictes:
                    if predicate in self.all_formated_predicates_in_merging_contexts:
                        return None, original_predicates
                return variable_index, original_predicates
        return None, original_predicates

    def revert_to_original_predicates(self, predicates):
        res = list()
        for predicate in predicates:
            predicate.replace(', inter1', '')
            res.append(predicate)
        return res


    def write_sas(self):
        sas_path = 'output.sas'
        string_builder = ''
        # 写prefix
        string_builder += 'begin_version\n'
        string_builder += '3\n'
        string_builder += 'end_version\n'
        string_builder += 'begin_metric\n'
        string_builder += '0\n'
        string_builder += 'end_metric\n'
        # 写variable
        string_builder += str(self.variable_num) + '\n'
        for var_index, predicates in self.variable_sas_format_predicate_map.items():
            string_builder += 'begin_variable\n'
            string_builder += 'var' + str(var_index) + '\n'
            string_builder += self.variable_axiom_map[var_index] + '\n'
            string_builder += str(len(predicates)) + '\n'
            for predicate in predicates:
                string_builder += predicate + '\n'
            string_builder += 'end_variable\n'
        string_builder += '0\n'
        # 写初始状态
        string_builder += 'begin_state\n'
        for i in range(self.variable_num):
            state = self.start_state[i]
            string_builder += str(state) + '\n'
        string_builder += 'end_state\n'
        # 写目标状态
        string_builder += 'begin_goal\n'
        string_builder += str(len(self.goal_state)) + '\n'
        for var_index, state in self.goal_state.items():
            string_builder += str(var_index) + ' ' + str(state) + '\n'
        string_builder += 'end_goal\n'
        # 写动作
        string_builder += str(len(self.action)) + '\n'
        for action, effects in self.action.items():
            string_builder += 'begin_operator\n'
            string_builder += action + '\n'
            if action in self.action_axiom_map.keys():
                string_builder += str(len(self.action_axiom_map[action])) + '\n'
                for axiom in self.action_axiom_map[action]:
                    string_builder += axiom + '\n'
            else:
                string_builder += '0\n'
            string_builder += str(len(effects)) + '\n'
            for effect in effects:
                string_builder += effect + '\n'
            string_builder += '1\n'
            string_builder += 'end_operator\n'
        # 写rule
        string_builder += str(self.get_rule_num()) + '\n'
        # empty rule
        for rule in self.empty_rule:
            string_builder += 'begin_rule\n'
            string_builder += '0\n'
            string_builder += rule + '\n'
            string_builder += 'end_rule\n'
        # 其他rule
        for rule_key, rules in self.rule.items():
            string_builder += 'begin_rule\n'
            string_builder += str(len(rules)) + '\n'
            for rule in rules:
                string_builder += rule + '\n'
            string_builder += rule_key + '\n'
            temp = rule_key.split(' ')
            string_builder += 'end_rule\n'
            for rule in rules:
                string_builder += 'begin_rule\n'
                string_builder += '1\n'
                r = rule.split(' ')
                old_value = int(r[1])
                if old_value == 0:
                    new_value = 1
                else:
                    new_value = 0
                string_builder += r[0] + ' ' + str(new_value) + '\n'
                string_builder += temp[0] + ' ' + temp[2] + ' ' + temp[1] + '\n'
                string_builder += 'end_rule\n'
        with open(sas_path, 'w') as f:
            f.write(string_builder)

    def get_rule_num(self):
        rule_num = 0
        for rule_key in self.rule.keys():
            rule_num += 1
            rule_num += len(self.rule[rule_key])
        return rule_num + len(self.empty_rule)


    def compute_plan(self, search_engine, keep_unreachable_facts=False):
        planner_path = './downward/fast-downward.py'
        if search_engine is None:
            if not keep_unreachable_facts:
                cmd = ['python3', planner_path, '--translate', self.classical_domain_file, self.classical_instance_file]
            else:
                cmd = ['python3', planner_path, '--translate', self.classical_domain_file, self.classical_instance_file, '--translate-options', '--keep-unreachable-facts']
            print(cmd)
            output = self.call_planner(cmd, 'PDDL', None)

            if output is not None and 'empty goal' in output:
                return 'empty goal'
            else:
                return 'success'
        else:
            if search_engine == 'LAMA-2011':
                cmd = ['python3', planner_path, '--alias', 'seq-sat-lama-2011', 'output.sas']
            else:
                cmd = ['python3', planner_path, 'output.sas', '--search', search_engine]
            output = self.call_planner(cmd, 'SAS', search_engine)
            if 'Search stopped without finding a solution.' in output:
                return 'Search stopped without finding a solution.'
            plan = extract_fd_plan(output)
            if plan is not None:
                return plan
            else:
                return None

    def call_planner(self, cmd, type, serch_engine):
        process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
        if type == 'PDDL' or (type == 'SAS' and serch_engine != 'LAMA-2011'):
            stdout = process.stdout.read()
            # print(stdout)
            stderr = process.stderr.read()
            print(stderr)
            if stderr == '' or 'WARNING' in stderr:
                return stdout
            elif 'Simplified to empty goal' in stdout:
                return 'empty goal'
            else:
                return None
        else:
            res = ''
            while process.poll() is None:
                stdout = process.stdout
                line = stdout.readline()
                line = line.strip()
                res += line + '\n'
                if 'Plan length' in line:
                    process.kill()
                    process.wait()
                    return res
            process.kill()
            process.wait()

    def generate_sas(self, generate_relaxed_task=False, output_sas=True):
        task = pddl_parser.open(self.classical_domain_file, self.classical_instance_file)
        normalize.normalize(task)
        if generate_relaxed_task:
            # Remove delete effects.
            for action in task.actions:
                for index, effect in reversed(list(enumerate(action.effects))):
                    if effect.literal.negated:
                        del action.effects[index]

        sas_task, actions = translate.pddl_to_sas(task, self.options)
        if output_sas and sas_task != 'Simplified to empty goal':
            with open("output.sas", "w") as output_file:
                sas_task.output(output_file)
        return sas_task, actions

    def delete_empty_plan(self, sample_list, problem, start_init):
        # 先修改domain
        self.classical_domain_file = self.classical_domain_file + '_no_empty'
        write_no_empty_plan_domain_file(problem, self.classical_domain_file)
        # 再修改instance
        self.classical_instance_file = self.classical_instance_file + '_no_empty'
        sample_list = sample_list[:-1]
        write_no_empty_plan_instance_file(problem, sample_list, start_init, self.classical_instance_file)
        return pddl_parser.open(self.classical_domain_file, self.classical_instance_file)


