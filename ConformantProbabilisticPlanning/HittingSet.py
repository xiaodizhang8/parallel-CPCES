from z3 import *
from pysat.examples.hitman import Hitman
import random
from django.db import OperationalError
import time




# def initialize(sample_tags_history, all_true_and_false_tags_by_index):
#     history_samples = copy.deepcopy(sample_tags_history)
#     all_tags = copy.deepcopy(all_true_and_false_tags_by_index)
#     all_tags_without_empty = []
#     for i in all_tags:
#         if len(i) != 0:
#             all_tags_without_empty.append(i)
#     all_sets = history_samples + all_tags_without_empty
#     h = Hitman(bootstrap_with=all_sets, htype='sorted')
#     return h
#
# def check_skipping(planning_task_id, hitting_task_id, sample_tags_history, all_true_and_false_tags_by_index, iteration, num_workers, used_hitting_sets):
#     h = initialize(sample_tags_history, all_true_and_false_tags_by_index)
#     hitting_task = HittingTask.objects.get(id=hitting_task_id)
#     hitting_task.status = 2
#     hitting_task.save()
#     this_round_hitting_sets = dict()
#     subtask_id_set = set()
#     for used_hitting in used_hitting_sets:
#         h.block(used_hitting)
#     while len(this_round_hitting_sets) < (num_workers):
#         hitting_set = h.get() # 这个函数自动实现了minimal的hitting set
#         if hitting_set is None:
#             # 最后结束时保存一下情况
#             hitting_task = HittingTask.objects.get(id=hitting_task_id)
#             hitting_task.this_round_hitting_sets = json.dumps(this_round_hitting_sets)
#             hitting_task.existed_task_ids = str(list(subtask_id_set))
#             hitting_task.status = 3
#             hitting_task.save(update_fields=['this_round_hitting_sets', 'existed_task_ids', 'status'])
#             break
#         hitting_set.sort()
#         res = check_existed_hitting_set(hitting_set, planning_task_id)
#         subtask_id_set = subtask_id_set | res # 搜集所有已经出现过的hitting set的task id
#         h.block(hitting_set)
#         this_round_hitting_sets[str(hitting_set)] = iteration # TODO: heuristic
#         hitting_task = HittingTask.objects.get(id=hitting_task_id)
#         hitting_task.this_round_hitting_sets = json.dumps(this_round_hitting_sets)
#         hitting_task.existed_task_ids = str(list(subtask_id_set))
#         hitting_task.save(update_fields=['this_round_hitting_sets', 'existed_task_ids'])
#     return None

import sys
import functools
import itertools
import operator
import subprocess

def write_cnf(hitting_problem, num_elements, blocked_sets, cnf_path):
    flatten_list = functools.reduce(operator.iconcat, hitting_problem, [])
    flatten_set = set(flatten_list)
    maximum = max(flatten_list)
    # num_elements = min(len(flatten_set), num_elements)

    cnf = ''
    index_num_map = dict()
    num_index_map = dict()
    num_clauses = 0
    total_index = maximum + 1
    for iteration in range(1, num_elements+1):
        this_round_index = []
        this_round_num_index_map = dict()
        for num in flatten_set:
            this_round_index.append(total_index)
            index_num_map[total_index] = num + 1 # 所有数字+1避免0的存在，因为0在cnf文件中代表clause的结束
            if num + 1 not in num_index_map.keys():
                num_index_map[num + 1] = {total_index}
            else:
                num_index_map[num + 1].add(total_index)
            this_round_num_index_map[num + 1] = total_index
            cnf += f"-{total_index} {num + 1} 0\n"
            num_clauses += 1
            total_index += 1
        combinations = itertools.combinations(this_round_index, 2)
        for combination in combinations:
            cnf += f"-{combination[0]} -{combination[1]} 0\n"
            num_clauses += 1

    for hitting_list in hitting_problem:
        clause = ''
        for num in hitting_list:
            clause += str(num + 1) + ' '
        clause += '0\n'
        cnf += clause
        num_clauses += 1

    for num, index_set in num_index_map.items():
        clause = str(num * (-1)) + ' '
        for index in index_set:
            clause += str(index) + ' '
        clause += '0\n'
        cnf += clause
        num_clauses += 1

    if len(blocked_sets) != 0:
        for blocked_set in blocked_sets:
            clause = ''
            for num in blocked_set:
                num = num + 1
                clause += str(num * (-1)) + ' '
            clause += '0\n'
            cnf += clause
            num_clauses += 1

    res = f"p cnf {total_index-1} {num_clauses}\n"
    res += cnf

    with open(cnf_path, 'w') as f:
        f.write(res)

    return index_num_map


def solve_sat_problem(cnf_file, hitting_task):
    kissat_path = './pCPCES/kissat-master/build/kissat'
    # kissat_path = './../kissat-master/build/kissat'
    cmd = [kissat_path, cnf_file]
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    hitter_pid = process.pid
    hitting_task.hitter_pid = hitter_pid
    retry_delay = 0.1
    while True:
        try:
            hitting_task.save(update_fields=['hitter_pid'])
            break
        except OperationalError as e:
            print('call_planner', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    stdout = process.stdout.read()
    stderr = process.stderr.read().strip()
    if stderr != '':
        print(stderr)
    return stdout
def extract_hitting_set(output, index_num_map):
    hitting_set = set()
    output = str(output).split('\n')
    for line in output:
        if line.startswith('s'):
            if 'UNSATISFIABLE' in line:
                return None
        if line.startswith('v'):
            line = line.split(' ')[1:]
            for index in line:
                index = int(index)
                if index in index_num_map.keys():
                    num = index_num_map[index] - 1
                    hitting_set.add(num)
    if len(hitting_set) != 0:
        return hitting_set
    else:
        return None


# def check_not_redundant(blocked_sets, new_set):
#     '''
#     因为这个方法会产生类似于{0,3}, {3}的多余的set（因为{3}是{0,3}的子集），需要筛一遍
#     '''
#     for blocked in blocked_sets:
#         intersect = blocked & new_set
#         if intersect == blocked or intersect == new_set:
#             return False
#     return True

def get_hitting_set(all_sets, num_elements, blocked_sets, iteration, hitting_task):
    '''
    由于num_elements设置为了最大值，所以只要是没有hitting set就是真没有hitting set了
    '''
    cnf_path = os.path.join('cnf_temp', 'test-' + str(iteration) + '.cnf')
    index_num_map = write_cnf(all_sets, num_elements, blocked_sets, cnf_path)
    stdout = solve_sat_problem(cnf_path, hitting_task)
    hs = extract_hitting_set(stdout, index_num_map)
    return hs
    # not_redundant = check_not_redundant(blocked_sets, hs)
    # blocked_sets.append(hs) # blocked要在check之后添加，否则出问题
    # if not_redundant:
    #     return hs


if __name__ == "__main__":
    blocked_sets = [[1,2]]
    index_num_map = write_cnf([[1,2,3], [2,3,4]], 20, blocked_sets, 'x.txt')
    # stdout = solve_sat_problem('test.cnf')
    # hs = extract_hitting_set(stdout, index_num_map)
    # print(hs)
    # not_redundant = check_not_redundant(blocked_sets, hs)
    # print(not_redundant)

# if __name__ == '__main__':
    # a = [{40}, {0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}, {32, 1, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}, {33, 2, 35, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47}]
    # a = [[0, 2, 3], [2, 3, 5]]

    # h = Hitman(bootstrap_with=a, htype='sorted')
    # h.block([4,3])
    # h.block([4,2])
    # h.block([4,0,5])
    # while True:
    #    a = h.get()
    #    print(a)
    #    h.block(a)