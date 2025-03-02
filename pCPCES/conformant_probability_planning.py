# -*- coding: utf-8 -*-
import sys
sys.path.append("..")

import os
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "parallel_CPCES.settings")
import django
django.setup()
from pCPCES.models import Task
# from pCPCES.models import TagTask
from pCPCES.translate.pddl_parser.pddl_file import open_pddl
from pCPCES.translate.instantiate import explore_probabilistic
from pCPCES.Methods.context import Context
from pCPCES.ConformantProbabilisticPlanning.AllProjectedProblems import AllProjectedProblems
from pCPCES.ConformantProbabilisticPlanning.TagGenerator import TagGenerator
from pCPCES.ConformantProbabilisticPlanning.MergedProblems import MergedProblems
from pCPCES.ConformantProbabilisticPlanning.Monitor import round_monitor
from pCPCES.ConformantProbabilisticPlanning.HittingSet import get_hitting_set
from pCPCES.ConformantProbabilisticPlanning.Z3StringConstraints import StringConstraints
from pCPCES.ConformantProbabilisticPlanning.TagProbability import TagProbability
from pCPCES.models import HittingTask
from django.db.models import Q
from itertools import islice
import time
import random
import multiprocessing
from multiprocessing import Process
import itertools
import copy
from pysat.examples.hitman import Hitman
import psutil
import signal
from pCPCES.ConformantProbabilisticPlanning.ClassicalPlanningWriter import write_classical_instance_file_by_hitting_set
from pCPCES.ConformantProbabilisticPlanning.ClassicalPlanningWriter import write_classical_domain_file_by_hitting_set
import os
from pCPCES.models import WorkerTask
from pCPCES.Methods.classical_planning import planning
import glob
import json
from django.db import OperationalError
import subprocess
from hashlib import sha256
from z3 import Solver
from z3 import sat
import math


def find_files(directory, file_pattern):
    # 构建搜索路径
    search_path = os.path.join(directory, file_pattern)
    # 使用 glob 查找匹配的文件
    matching_files = glob.glob(search_path)
    return matching_files

merged_problems_history = []
merge_problem_map = dict()

def start_planning(processing_index, selected_task):
    pid = os.getpid()
    selected_task.pool_index = processing_index
    selected_task.pid = pid
    selected_task.status = 2
    retry_delay = 0.1
    while True:
        try:
            selected_task.save(update_fields=['pool_index', 'pid', 'status'], force_update=True)
            break
        except OperationalError as e:
            print('start_planning2', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    classical_domain_path = selected_task.classical_domain_path
    classical_instance_path = selected_task.classical_instance_path
    planner = selected_task.planner
    search_engine = selected_task.search_engine
    planning(classical_domain_path, classical_instance_path, planner, selected_task, search_engine)

def error_callback(e):
    print(f"Task failed with error: {e}")

def monitor_planning_processing(num_workers_planning, planning_task):
    num_processings = num_workers_planning
    pool = multiprocessing.Pool(num_processings)
    processing_index = 0
    current_iteration = 1
    while True:
        newest_files = find_files(os.path.join('files', str(planning_task.id), 'planning'), str(current_iteration)+'-*.txt')
        if len(newest_files) > 0 and (len(pool._cache) < num_processings or pool._cache is None):
            retry_delay = 0.1
            while True:
                try:
                    waiting_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(
                        Q(task=planning_task) & Q(status=1)).order_by('-iteration', 'weight')
                    num_waiting_tasks = len(waiting_tasks)
                    break
                except OperationalError as e:
                    print('monitor_planning_processing 1', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            if num_waiting_tasks > 0:
                for index in range(num_waiting_tasks):
                    selected_task = waiting_tasks[index]
                    selected_task_id = selected_task.id
                    if index == 0 and selected_task.iteration==current_iteration and (len(pool._cache) < num_processings or pool._cache is None):
                        if os.path.exists(
                                os.path.join('files', str(planning_task.id), 'planning',
                                             str(selected_task.iteration) + '-' + str(
                                                 selected_task_id) + '.txt')):
                            pool.apply_async(start_planning,
                                             (processing_index, selected_task), error_callback=error_callback)
                            processing_index += 1
                            with open(os.path.join('files', str(planning_task.id), 'is_planning',
                                                   str(selected_task.iteration) + '-' + str(
                                                       selected_task_id) + '.txt'), 'w') as f:
                                f.write(str(selected_task.iteration) + '-' + str(selected_task_id))
                            os.remove(os.path.join('files', str(planning_task.id), 'planning',
                                                   str(selected_task.iteration) + '-' + str(
                                                       selected_task_id) + '.txt'))
                            current_iteration += 1
                    elif index > 0 and (len(pool._cache) < num_processings - 1 or pool._cache is None):
                        if os.path.exists(
                                os.path.join('files', str(planning_task.id), 'planning',
                                             str(selected_task.iteration) + '-' + str(
                                                 selected_task_id) + '.txt')):
                            pool.apply_async(start_planning,
                                             (processing_index, selected_task), error_callback=error_callback)
                            processing_index += 1
                            with open(os.path.join('files', str(planning_task.id), 'is_planning',
                                                   str(selected_task.iteration) + '-' + str(
                                                       selected_task_id) + '.txt'), 'w') as f:
                                f.write(str(selected_task.iteration) + '-' + str(selected_task_id))
                            os.remove(os.path.join('files', str(planning_task.id), 'planning',
                                                   str(selected_task.iteration) + '-' + str(
                                                       selected_task_id) + '.txt'))
                            if selected_task.iteration == current_iteration:
                                current_iteration += 1
                    else:
                        break
        elif len(newest_files) == 0 and (len(pool._cache) < num_processings - 1 or pool._cache is None):
            retry_delay = 0.1
            while True:
                try:
                    waiting_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(
                        Q(task=planning_task) & Q(status=1)).order_by('-iteration', 'weight')
                    num_waiting_tasks = len(waiting_tasks)
                    break
                except OperationalError as e:
                    print('monitor_planning_processing 1', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            if num_waiting_tasks > 0:
                for index in range(num_waiting_tasks):
                    selected_task = waiting_tasks[index]
                    selected_task_id = selected_task.id
                    if os.path.exists(
                            os.path.join('files', str(planning_task.id), 'planning',
                                         str(selected_task.iteration) + '-' + str(
                                             selected_task_id) + '.txt')) and (len(pool._cache) < num_processings - 1 or pool._cache is None):
                        pool.apply_async(start_planning,
                                         (processing_index, selected_task), error_callback=error_callback)
                        processing_index += 1
                        if selected_task.iteration == current_iteration:
                            current_iteration += 1
                        with open(os.path.join('files', str(planning_task.id), 'is_planning',
                                               str(selected_task.iteration) + '-' + str(
                                                   selected_task_id) + '.txt'), 'w') as f:
                            f.write(str(selected_task.iteration) + '-' + str(selected_task_id))
                        os.remove(os.path.join('files', str(planning_task.id), 'planning',
                                               str(selected_task.iteration) + '-' + str(
                                                   selected_task_id) + '.txt'))
                    elif not (len(pool._cache) < num_processings - 1 or pool._cache is None):
                        break


def monitor_hitting_processing(problem, planning_task, num_workers_hitting, num_workers_planning,
                             hitting_batch_size, hitting_search_method, incremental_tags,
                             planning_task_id,
                             domain_dir_path,
                             instance_name,
                             instance_dir_path,
                             probabilistic_tag_generator,
                             all_projected_problems,
                             contexts, domain_name, planner,
                             search_engine):
    num_processings = num_workers_hitting
    hitting_pool = multiprocessing.Pool(num_processings)
    processing_index = 0
    applied_files = 0
    while True:
        files = os.listdir(os.path.join('files', str(planning_task_id), 'hitting'))
        if len(files) > applied_files:
            retry_delay = 0.1
            # 将新进程添加到list中，并启动
            while True:
                try:
                    waiting_tasks = HittingTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(status=1))
                    num_waiting_tasks = len(waiting_tasks)
                    break
                except OperationalError as e:
                    print('monitor_hitting_processing 1', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue

            if num_waiting_tasks != 0:
                retry_delay = 0.1
                while True:
                    try:
                        waiting_task = waiting_tasks.first()
                        break
                    except OperationalError as e:
                        print('monitor_hitting_processing 3', e)
                        time.sleep(retry_delay)
                        retry_delay *= 1 + random.random() * 0.5
                        continue
                iteration = waiting_task.iteration
                sample_tags_history = eval(waiting_task.sample_tags_history)
                used_projected_problems = eval(waiting_task.used_projected_problems)
                used_projected_problems.sort()
                if incremental_tags:
                    hitting_pool.apply_async(incremental_tags_set)
                else:
                    hitting_pool.apply_async(search_hitting_sets, (
                        problem, processing_index, num_workers_planning, planning_task_id, waiting_task, sample_tags_history,
                        iteration, num_workers_hitting, domain_dir_path,
                        instance_name,
                        instance_dir_path, probabilistic_tag_generator, all_projected_problems, contexts,
                        planning_task,
                        domain_name, planner, search_engine, hitting_batch_size, hitting_search_method, used_projected_problems), error_callback=error_callback)
                processing_index += 1
                applied_files += 1


def monitor_first_priority_sample_tags_processing(problem, num_workers_tags, planning_task, action_map, contexts, probabilistic_tag_generator, all_projected_problems, total_time_start, threshold):
    if num_workers_tags == 1:
        num_processings = 1
    else:
        num_processings = num_workers_tags // 2
    sample_tag_pool = multiprocessing.Pool(num_processings)
    applied_files = 0
    while True:
        result_queue1 = multiprocessing.Manager().Queue()
        files = os.listdir(os.path.join('files', str(planning_task.id), 'has_plan'))
        if len(files) > applied_files:
            if len(sample_tag_pool._cache) < num_processings or sample_tag_pool._cache is None:
                retry_delay = 0.1
                while True:
                    try:
                        waiting_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(status=3) & Q(plan__isnull=False) & Q(has_sample_tags__isnull=True) & Q(first_priority=0)).order_by('-iteration', 'weight')
                        num_waiting_tasks = len(waiting_tasks)
                        break
                    except OperationalError as e:
                        print('monitor_sample_tags_processing 1', e)
                        time.sleep(retry_delay)
                        retry_delay *= 1 + random.random() * 0.5
                        continue
                if num_waiting_tasks > 0:
                    applied_files += 1
                    selected_task = waiting_tasks[0]
                    candidate_plan = eval(selected_task.plan)
                    has_enough_tags = False
                    number_of_sample_tags = 0
                    used_projected_problems_for_sample_tags = set()


                    sample_tags = list()
                    final_probability = 0
                    for i in range(len(all_projected_problems.all_projected_problems)):
                        sample_tags.append(None)

                    all_tags_in_one_list = copy.deepcopy(probabilistic_tag_generator.all_tags_in_one_list)
                    random.shuffle(all_tags_in_one_list)
                    if len(all_tags_in_one_list) > num_processings:
                        all_tags_in_one_list = split_list(all_tags_in_one_list, num_processings)
                    else:
                        all_tags_in_one_list = split_list(all_tags_in_one_list, len(all_tags_in_one_list))
                    for tag_list in all_tags_in_one_list:
                        sample_tag_pool.apply_async(check_counter_tag, (probabilistic_tag_generator, all_projected_problems, problem, candidate_plan, action_map, contexts,tag_list, result_queue1))
                    while (len(sample_tag_pool._cache) != 0 or result_queue1.qsize() > 0) and not has_enough_tags:
                        if result_queue1.qsize() > 0:
                            tag = result_queue1.get()
                            pro_index = probabilistic_tag_generator.tag_subproblem_index_map[get_hash_code(tag)]
                            if sample_tags[pro_index] is None:
                                sample_tags[pro_index] = [tag]
                            else:
                                sample_tags[pro_index].append(tag)
                            if threshold is not None:
                                used_projected_problems_for_sample_tags.add(pro_index)
                                temp = list(used_projected_problems_for_sample_tags)
                                temp.sort()
                                if str(temp) in merge_problem_map.keys():
                                    mp_sample = merge_problem_map[str(temp)]
                                else:
                                    mp_sample = MergedProblems(all_projected_problems,
                                                               used_projected_problems_for_sample_tags, problem)
                                    mp_sample.merge_problems()
                                    merge_problem_map[str(temp)] = mp_sample
                                tp = TagProbability(problem, candidate_plan, action_map, contexts,
                                                    probabilistic_tag_generator, mp_sample)
                                counter_tags_probability = compute_multi_tags_probability(sample_tags, tp)
                                if counter_tags_probability > 1:
                                    print('概率大于1，有bug！')
                                    print('last tag', tag)
                                    print('sample tags', sample_tags)
                                    print('sample tags probability', counter_tags_probability)
                                    kill_all_processings()
                                final_probability = counter_tags_probability
                                if counter_tags_probability > 1 - threshold:
                                    update_database_workertask_info(sample_tags, final_probability, probabilistic_tag_generator,
                                                                    selected_task)
                                    has_enough_tags = True
                                    break
                    if not has_enough_tags:
                        update_database_workertask_info(None, final_probability, probabilistic_tag_generator,
                                                        selected_task)
                        print('没有足够多的sample tag')
                        print('find a valid plan')
                        print(candidate_plan)
                        print('plan length', len(candidate_plan))
                        total_time = time.time() - total_time_start
                        print('iteration', selected_task.iteration)
                        print('total time:', total_time)
                        kill_all_processings()


def monitor_normal_sample_tags_processing(problem, num_workers_tags, planning_task, action_map, contexts,
                                                  probabilistic_tag_generator, all_projected_problems, total_time_start,
                                                  threshold):
    if num_workers_tags == 1:
        return
    num_processings = num_workers_tags // 2
    sample_tag_pool = multiprocessing.Pool(num_processings)
    applied_files = 0
    while True:
        result_queue2 = multiprocessing.Manager().Queue()
        files = os.listdir(os.path.join('files', str(planning_task.id), 'has_plan'))
        if len(files) > applied_files:
            if len(sample_tag_pool._cache) < num_processings or sample_tag_pool._cache is None:
                retry_delay = 0.1
                while True:
                    try:
                        waiting_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(
                            Q(task=planning_task) & Q(status=3) & Q(plan__isnull=False) & Q(
                                has_sample_tags__isnull=True) & Q(first_priority=1)).order_by('-iteration', 'weight')
                        num_waiting_tasks = len(waiting_tasks)
                        break
                    except OperationalError as e:
                        print('monitor_sample_tags_processing 1', e)
                        time.sleep(retry_delay)
                        retry_delay *= 1 + random.random() * 0.5
                        continue
                if num_waiting_tasks > 0:
                    selected_task = waiting_tasks[0]
                    applied_files += 1
                    candidate_plan = eval(selected_task.plan)
                    has_enough_tags = False
                    number_of_sample_tags = 0
                    used_projected_problems_for_sample_tags = set()

                    sample_tags = list()
                    final_probability = 0
                    for i in range(len(all_projected_problems.all_projected_problems)):
                        sample_tags.append(None)

                    all_tags_in_one_list = copy.deepcopy(probabilistic_tag_generator.all_tags_in_one_list)
                    random.shuffle(all_tags_in_one_list)
                    if len(all_tags_in_one_list) > num_processings:
                        all_tags_in_one_list = split_list(all_tags_in_one_list, num_processings)
                    else:
                        all_tags_in_one_list = split_list(all_tags_in_one_list, len(all_tags_in_one_list))
                    for tag_list in all_tags_in_one_list:
                        sample_tag_pool.apply_async(check_counter_tag, (
                        probabilistic_tag_generator, all_projected_problems, problem, candidate_plan, action_map,
                        contexts, tag_list, result_queue2))
                    while (len(sample_tag_pool._cache) != 0 or result_queue2.qsize() > 0) and not has_enough_tags:
                        if result_queue2.qsize() > 0:
                            tag = result_queue2.get()
                            pro_index = probabilistic_tag_generator.tag_subproblem_index_map[get_hash_code(tag)]
                            if sample_tags[pro_index] is None:
                                sample_tags[pro_index] = [tag]
                            else:
                                sample_tags[pro_index].append(tag)
                            if threshold is not None:
                                used_projected_problems_for_sample_tags.add(pro_index)
                                temp = list(used_projected_problems_for_sample_tags)
                                temp.sort()
                                if str(temp) in merge_problem_map.keys():
                                    mp_sample = merge_problem_map[str(temp)]
                                else:
                                    mp_sample = MergedProblems(all_projected_problems,
                                                               used_projected_problems_for_sample_tags, problem)
                                    mp_sample.merge_problems()
                                    merge_problem_map[str(temp)] = mp_sample
                                tp = TagProbability(problem, candidate_plan, action_map, contexts,
                                                    probabilistic_tag_generator, mp_sample)
                                counter_tags_probability = compute_multi_tags_probability(sample_tags, tp)
                                if counter_tags_probability > 1:
                                    print('概率大于1，有bug！')
                                    print('last tag', tag)
                                    print('sample tags', sample_tags)
                                    print('sample tags probability', counter_tags_probability)
                                    kill_all_processings()
                                final_probability = counter_tags_probability
                                if counter_tags_probability > 1 - threshold:
                                    update_database_workertask_info(sample_tags, final_probability,
                                                                    probabilistic_tag_generator,
                                                                    selected_task)
                                    has_enough_tags = True
                                    break
                    if not has_enough_tags:
                        update_database_workertask_info(None, final_probability, probabilistic_tag_generator,
                                                        selected_task)
                        print('没有足够多的sample tag')
                        print('find a valid plan')
                        print(candidate_plan)
                        print('plan length', len(candidate_plan))
                        total_time = time.time() - total_time_start
                        print('iteration', selected_task.iteration)
                        print('total time:', total_time)
                        kill_all_processings()



def compute_sample_tags(selected_task, problem, candidate_plan, action_map, contexts, probabilistic_tag_generator, all_projected_problems, total_time_start, threshold):
    # 判断每个tag是否符合sample tag

    sample_tags, probability = find_sample_tags(problem, eval(candidate_plan), action_map, contexts, probabilistic_tag_generator, all_projected_problems, selected_task, total_time_start, threshold)
    # update_database_workertask_info(sample_tags, probability, probabilistic_tag_generator, planning_task_id)


def find_sample_tags(problem, candidate_plan, action_map, contexts, tag_generator, all_projected_problems, selected_task, total_time_start, threshold=None):
    number_of_sample_tags = 0
    used_projected_problems_for_sample_tags = set()
    return find_random_sample_tags(problem, candidate_plan, action_map, contexts, tag_generator, all_projected_problems, number_of_sample_tags, used_projected_problems_for_sample_tags, selected_task, total_time_start, threshold=threshold)

def get_hash_code(s):
    return sha256(str(s).encode('utf-8')).hexdigest()

def compute_multi_tags_probability(sample_tags, tp):
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

def get_information_from_sample_tags_for_hitting_set(tag_index_map, sample_tags):
    res_num = 0
    sample_tag_index = []
    res_used_projected_problems = set()
    for i in range(len(sample_tags)):
        group = sample_tags[i]
        if group is not None:
            for sample_tag in group:
                sample_tag.sort()
                index = tag_index_map[get_hash_code(sample_tag)]
                sample_tag_index.append(index)
                res_num += 1
                res_used_projected_problems.add(i)
    sample_tag_index.sort()
    return res_num, list(res_used_projected_problems), sample_tag_index



def split_list(lst, n):
    it = iter(lst)
    return [list(islice(it, i)) for i in [len(lst) // n + (1 if x < len(lst) % n else 0) for x in range(n)]]


def find_random_sample_tags(problem, candidate_plan, action_map, contexts, tag_generator, all_projected_problems, number_of_sample_tags, used_projected_problems_for_sample_tags, selected_task, total_time_start, threshold=None):
    '''
    随机抽取sample tags
    :param threshold:
    :return:
    '''
    import queue
    result_queue = queue.Queue()

    sample_tags = list()
    final_probability = 0
    for i in range(len(all_projected_problems.all_projected_problems)):
        sample_tags.append(None)

    all_tags_in_one_list = copy.deepcopy(tag_generator.all_tags_in_one_list)
    random.shuffle(all_tags_in_one_list)
    if len(all_tags_in_one_list) >1:
        all_tags_in_one_list = split_list(all_tags_in_one_list, 2)
    else:
        all_tags_in_one_list = split_list(all_tags_in_one_list, len(all_tags_in_one_list))

    threads = []
    for tag_list in all_tags_in_one_list:
        thread = Process(target=check_counter_tag, args=(tag_generator, all_projected_problems, problem, candidate_plan, action_map, contexts, tag_list, result_queue))
        threads.append(thread)
        thread.start()

    while threads_isalive(threads):
        print('alive')
        if result_queue.qsize() > 0:
            print('tag')
            tag = result_queue.get()
            print(1)
            pro_index = tag_generator.tag_subproblem_index_map[get_hash_code(tag)]
            if sample_tags[pro_index] is None:
                sample_tags[pro_index] = [tag]
            else:
                sample_tags[pro_index].append(tag)
            if threshold is not None:
                used_projected_problems_for_sample_tags.add(pro_index)
                temp = list(used_projected_problems_for_sample_tags)
                temp.sort()
                if str(temp) in merge_problem_map.keys():
                    mp_sample = merge_problem_map[str(temp)]
                else:
                    mp_sample = MergedProblems(all_projected_problems,
                                               used_projected_problems_for_sample_tags, problem)
                    mp_sample.merge_problems()
                    merge_problem_map[str(temp)] = mp_sample
                tp = TagProbability(problem, candidate_plan, action_map, contexts,
                                    tag_generator, mp_sample)
                counter_tags_probability = compute_multi_tags_probability(sample_tags, tp)
                if counter_tags_probability > 1:
                    print('概率大于1，有bug！')
                    print('last tag', tag)
                    print('sample tags', sample_tags)
                    print('sample tags probability', counter_tags_probability)
                    kill_all_processings()
                final_probability = counter_tags_probability
                print(final_probability)
                if counter_tags_probability > 1 - threshold:
                    update_database_workertask_info(sample_tags, final_probability, tag_generator,
                                                    selected_task)
                    for thread in threads:
                        thread.join()
                    return sample_tags, final_probability
    update_database_workertask_info(None, final_probability, tag_generator,
                                    selected_task)
    print('没有足够多的sample tag')
    print('find a valid plan')
    print(candidate_plan)
    print('plan length', len(candidate_plan))
    total_time = time.time() - total_time_start
    print('iteration', selected_task.iteration)
    print('total time:', total_time)
    kill_all_processings()

def threads_isalive(threads):
    for t in threads:
        if t.is_alive():
            return True
    return False

def check_counter_tag(tag_generator, all_projected_problems, problem, candidate_plan, action_map, contexts, tag_list, result_queue):
    for tag in tag_list:
        pro_index = tag_generator.tag_subproblem_index_map[get_hash_code(tag)]
        projected_problem = all_projected_problems.all_projected_problems[pro_index]
        constant_problem = all_projected_problems.constant_problem
        constraint_object = StringConstraints(problem, candidate_plan, action_map,
                                              contexts, tag_generator, projected_problem, constant_problem)
        regression_assert = ''
        if candidate_plan is not None:
            constraint_object.regression(problem, candidate_plan, action_map)
            regression_assert = constraint_object.get_regression_assert()
        precondition_assert = constraint_object.get_projected_precondition_assert()
        initial_assert = constraint_object.get_projected_initial_assert()  # 不需要initial assert，但是需要initial的declare
        constraint_string = [regression_assert, precondition_assert]
        tag_assert = '(assert (and '
        for item in tag_generator.all_true_and_false_tags[pro_index]:
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
            result_queue.put(tag)


def sample_tag_index_to_sample_tag(sample_tags_index, tag_generator):
    sample_tags = []
    index_tag_map = tag_generator.index_tag_map
    for group in sample_tags_index:
        if group is None:
            sample_tags.append(None)
        else:
            sample_group = []
            for index in group:
                tag = index_tag_map[index]
                sample_group.append(tag)
            sample_tags.append(sample_group)
    return sample_tags


def update_database_workertask_info(sample_tags, probability, probabilistic_tag_generator, worker):
    # has_sample_tags = False
    used_projected_problems = None
    sample_tag_index = None
    if sample_tags is not None:
        # real_sample_tags = sample_tag_index_to_sample_tag(sample_tags_index_group,
        #                                                   probabilistic_tag_generator)  # 这个才是真正的tag，因为index不能用于算概率

        num_of_sample_tags, used_projected_problems, sample_tag_index = get_information_from_sample_tags_for_hitting_set(
            probabilistic_tag_generator.tag_index_map, sample_tags)
    # retry_delay = 0.1
    # while True:
    #     try:
    #         workers = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id=selected_worker_task_id))
    #         if len(workers) != 0:
    #             worker = workers[0]
    #             break
    #     except OperationalError as e:
    #         print('compute_sample_tags 3', e)
    #         time.sleep(retry_delay)
    #         retry_delay *= 1 + random.random() * 0.5
    #         continue
    worker.sample_tag_index = json.dumps(sample_tag_index)
    if sample_tags is not None:
        worker.has_sample_tags = True
        # has_sample_tags = True
    else:
        worker.has_sample_tags = False
        # has_sample_tags = False
    worker.tags_probability = probability

    worker.used_projected_problems = json.dumps(used_projected_problems)
    worker.status = 4
    retry_delay = 0.1
    while True:
        try:
            worker.save(update_fields=['sample_tag_index', 'has_sample_tags', 'tags_probability', 'used_projected_problems', 'status'], force_update=True)
            break
        except OperationalError as e:
            print('compute_sample_tags 5', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    with open(os.path.join('files', str(worker.task_id), 'tag_finished', str(worker.iteration)+'_'+str(worker.id)+'.txt'), 'w') as f:
        f.write(str(worker.iteration)+'_'+str(worker.id))
    # return has_sample_tags, used_projected_problems

def update_first_priority(worker_task):
    # retry_delay = 0.1
    # while True:
    #     try:
    #         worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id=selected_worker_task_id))
    #         if len(worker_tasks) != 0:
    #             worker_task = worker_tasks[0]
    #         break
    #     except OperationalError as e:
    #         print('update_first_priority 1', e)
    #         time.sleep(retry_delay)
    #         retry_delay *= 1 + random.random() * 0.5
    #         continue
    worker_task.first_priority = 0
    retry_delay = 0.1
    while True:
        try:
            worker_task.save(update_fields=['first_priority'], force_update=True)
            break
        except OperationalError as e:
            print('update_first_priority 2', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue


def get_action_map(actions, result):
    for action in actions:
        result[action.name] = action
    return result

def merge_counter_examples(counter_examples_records, new_counter_examples):
    for counter_example in new_counter_examples:
        if counter_example not in counter_examples_records:
            counter_examples_records.append(counter_example)
    return counter_examples_records

def get_counter_example_index(counter_examples_records, new_counter_examples):
    res = list()
    for counter_example in new_counter_examples:
        index = counter_examples_records.index(counter_example)
        res.append(index)
    return res


def modify_contexts(all_projected_problems, contexts, merging_contexts):

    removed_contexts = []
    removed_merged_contexts = []
    for index in range(len(all_projected_problems.all_projected_problems)):
        projected_problem = all_projected_problems.all_projected_problems[index]
        if len(projected_problem.goal) == 0:
            removed_contexts.append(index)
            removed_merged_contexts.append(index)
    for i in removed_contexts:
        contexts.contexts[i] = None
    for i in removed_merged_contexts:
        merging_contexts.contexts[i] = None


def initialize_hitman(sample_tags_history, all_true_and_false_tags_by_index):
    history_samples = copy.deepcopy(sample_tags_history)
    all_tags = copy.deepcopy(all_true_and_false_tags_by_index)
    all_tags_without_empty = []
    for i in all_tags:
        if len(i) != 0:
            all_tags_without_empty.append(i)
    all_sets = history_samples + all_tags_without_empty
    h = Hitman(bootstrap_with=all_sets, htype='sorted')
    return h




def search_hitting_sets(problem, processing_index, num_workers_planning, planning_task_id, hitting_task, sample_tags_history,
                    iteration, num_workers_hitting, domain_dir_path,
                    instance_name,
                    instance_dir_path, probabilistic_tag_generator, all_projected_problems, contexts,
                    planning_task,
                    domain_name, planner, search_engine, hitting_batch_size, hitting_search_method, used_projected_problems):
    # print('hitting search start for iteration', iteration)
    num_tags = len(probabilistic_tag_generator.all_tags_in_one_list)
    expected_tag_num = math.floor(num_tags * problem.threshold * 0.7)


    all_true_and_false_tags_by_index = probabilistic_tag_generator.all_true_and_false_tags_by_index
    all_tags_in_one_list = probabilistic_tag_generator.all_tags_in_one_list
    all_index = probabilistic_tag_generator.all_index
    history_samples = copy.deepcopy(sample_tags_history)
    all_tags = copy.deepcopy(all_true_and_false_tags_by_index)
    all_tags_without_empty = []
    for i in all_tags:
        if len(i) != 0:
            all_tags_without_empty.append(i)
    all_sets = history_samples + all_tags_without_empty
    blocked_hitting_sets = []
    num_elements = len(all_sets)
    h = None
    if hitting_search_method == 'hitman':
        h = initialize_hitman(sample_tags_history, all_true_and_false_tags_by_index)
    task_pid = os.getpid()
    existed_task_ids = eval(hitting_task.existed_task_ids)
    # hitting_task = waiting_task
    # existed_task_ids = eval(hitting_task.existed_task_ids)
    hitting_task.pid = task_pid
    hitting_task.pool_index = processing_index
    hitting_task.status = 2
    retry_delay = 0.1
    while True:
        try:
            hitting_task.save(update_fields=['pid', 'pool_index', 'status'], force_update=True)
            break
        except OperationalError as e:
            print('search_hitting_sets 2', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    if str(used_projected_problems) in merge_problem_map.keys():
        mp = merge_problem_map[str(used_projected_problems)]
    else:
        mp = MergedProblems(all_projected_problems, used_projected_problems, problem)
        mp.merge_problems()
        merge_problem_map[str(used_projected_problems)] = mp
    # print('finished merging')
    merged_problems_history.append(mp)
    this_round_merged_problems = merged_problems_history.copy()
    this_round_hitting_sets_num = hitting_task.this_round_hitting_sets_num
    this_round_existed_num = 0
    print('进入hitting搜索环节')
    num_additional_tags_in_hitting = 0
    previous_root_hitting_set = None
    files = os.listdir(os.path.join('files', str(planning_task_id), 'hitting'))
    if str(iteration + num_workers_hitting) + '.txt' in files:
        return
    while True:
        if hitting_search_method == 'hitman':
            hitting_set = h.get()  # 这个函数自动实现了minimal的hitting set
            # h.block(hitting_set)
        else:
            hitting_set = get_hitting_set(all_sets, num_elements, blocked_hitting_sets, iteration, hitting_task)
        num_additional_tags_in_hitting += 1
        previous_root_hitting_set = hitting_set
        if hitting_set is None:
            hitting_task.status = 3
            retry_delay = 0.1
            while True:
                try:
                    hitting_task.save(update_fields=['status'], force_update=True)
                    print('hitting search finished for iteration', iteration)
                    break
                except OperationalError as e:
                    print('search_hitting_sets 4', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            with open(os.path.join('files', str(planning_task_id), 'hitting_finished', str(iteration) + '.txt'), 'w') as f:
                f.write(str(iteration))
            return
        else:
            hitting_set = list(hitting_set)
            hitting_set.sort()
            blocked_hitting_sets.append(hitting_set)
            this_round_hitting_sets_num += 1
            res = check_existed_hitting_set(hitting_set, planning_task_id, iteration)
            if len(res) != 0:
                this_round_existed_num += 1
                for subtask_id in res:
                    existed_task_ids.append(subtask_id)
                hitting_task.existed_task_ids = str(existed_task_ids)
                hitting_task.this_round_hitting_sets_num = this_round_hitting_sets_num
                retry_delay = 0.1
                while True:
                    try:
                        hitting_task.save(update_fields=['existed_task_ids', 'this_round_hitting_sets_num'],
                                          force_update=True)
                        break
                    except OperationalError as e:
                        print('search_hitting_sets 5', e)
                        time.sleep(retry_delay)
                        retry_delay *= 1 + random.random() * 0.5
                        continue
            priority = compute_priority(hitting_set, contexts, probabilistic_tag_generator)
            hitting_set_info = (hitting_set, priority)
            add_worker_task(hitting_set_info, domain_dir_path, instance_name, iteration, instance_dir_path, problem,
                            this_round_merged_problems, probabilistic_tag_generator, all_projected_problems, contexts,
                            planning_task, domain_name, planner, search_engine)

                # # 额外加一个tag
                # files = os.listdir(os.path.join('files', str(planning_task_id), 'hitting'))
                # if str(iteration + num_workers_hitting) + '.txt' in files:
                #     return
                # candidate_tag_index = all_index - previous_root_hitting_set
                # if len(candidate_tag_index) == 0:
                #     hitting_task.status = 3
                #     retry_delay = 0.1
                #     while True:
                #         try:
                #             hitting_task.save(update_fields=['status'], force_update=True)
                #             print('hitting search finished for iteration', iteration)
                #             break
                #         except OperationalError as e:
                #             print('search_hitting_sets 4', e)
                #             time.sleep(retry_delay)
                #             retry_delay *= 1 + random.random() * 0.5
                #             continue
                #     with open(os.path.join('files', str(planning_task_id), 'hitting_finished', str(iteration) + '.txt'),
                #               'w') as f:
                #         f.write(str(iteration))
                #     return
                #
                # added_num = min(2, len(candidate_tag_index))
                # added_num = random.randint(1, added_num)
                # additional_tags = random.sample(candidate_tag_index, added_num)
                # branch_hitting_set = previous_root_hitting_set | set(additional_tags)
                # hitting_set = list(branch_hitting_set)
                # hitting_set.sort()
                # if hitting_set in blocked_hitting_sets:
                #     continue
                # this_round_hitting_sets_num += 1
                # blocked_hitting_sets.append(hitting_set)
                # res = check_existed_hitting_set(hitting_set, planning_task_id, iteration)
                # if len(res) != 0:
                #     this_round_existed_num += 1
                #     for subtask_id in res:
                #         existed_task_ids.append(subtask_id)
                #     hitting_task.existed_task_ids = str(existed_task_ids)
                #     retry_delay = 0.1
                #     while True:
                #         try:
                #             hitting_task.save(update_fields=['existed_task_ids'],
                #                               force_update=True)
                #             break
                #         except OperationalError as e:
                #             print('search_hitting_sets 5', e)
                #             time.sleep(retry_delay)
                #             retry_delay *= 1 + random.random() * 0.5
                #             continue
                # priority = compute_priority(hitting_set, contexts, probabilistic_tag_generator)
                # hitting_set_info = (hitting_set, priority)
                # add_worker_task(hitting_set_info, domain_dir_path, instance_name, iteration, instance_dir_path, problem,
                #                 this_round_merged_problems, probabilistic_tag_generator, all_projected_problems, contexts,
                #                 planning_task, domain_name, planner, search_engine)


        #
        # candidate_tag_index = all_index - previous_root_hitting_set
        # if len(candidate_tag_index) == 0:
        #     hitting_task.status = 3
        #     retry_delay = 0.1
        #     while True:
        #         try:
        #             hitting_task.save(update_fields=['status'], force_update=True)
        #             print('hitting search finished for iteration', iteration)
        #             break
        #         except OperationalError as e:
        #             print('search_hitting_sets 4', e)
        #             time.sleep(retry_delay)
        #             retry_delay *= 1 + random.random() * 0.5
        #             continue
        #     with open(os.path.join('files', str(planning_task_id), 'hitting_finished', str(iteration) + '.txt'), 'w') as f:
        #         f.write(str(iteration))
        #     return
        #
        # max_random_num = (2 ** len(candidate_tag_index) - 1) // 2
        # while this_round_hitting_sets_num < max_random_num:
        #     files = os.listdir(os.path.join('files', str(planning_task_id), 'hitting'))
        #     if str(iteration + num_workers_hitting) + '.txt' in files:
        #         return
        #     sample_size = random.randint(1, len(candidate_tag_index))
        #     additional_tags = random.sample(candidate_tag_index, sample_size)
        #     branch_hitting_set = previous_root_hitting_set | set(additional_tags)
        #     hitting_set = list(branch_hitting_set)
        #     hitting_set.sort()
        #     if hitting_set in blocked_hitting_sets:
        #         continue
        #     this_round_hitting_sets_num += 1
        #     blocked_hitting_sets.append(hitting_set)
        #     res = check_existed_hitting_set(hitting_set, planning_task_id, iteration)
        #     if len(res) != 0:
        #         this_round_existed_num += 1
        #         for subtask_id in res:
        #             existed_task_ids.append(subtask_id)
        #         hitting_task.existed_task_ids = str(existed_task_ids)
        #         retry_delay = 0.1
        #         while True:
        #             try:
        #                 hitting_task.save(update_fields=['existed_task_ids'],
        #                                   force_update=True)
        #                 break
        #             except OperationalError as e:
        #                 print('search_hitting_sets 5', e)
        #                 time.sleep(retry_delay)
        #                 retry_delay *= 1 + random.random() * 0.5
        #                 continue
        #     priority = compute_priority(hitting_set, contexts, probabilistic_tag_generator)
        #     hitting_set_info = (hitting_set, priority)
        #     add_worker_task(hitting_set_info, domain_dir_path, instance_name, iteration, instance_dir_path, problem,
        #                     this_round_merged_problems, probabilistic_tag_generator, all_projected_problems, contexts,
        #                     planning_task, domain_name, planner, search_engine)
        #     if this_round_hitting_sets_num % num_workers_planning * 3 == 0:
        #         time.sleep(1)
        #
        # for sample_size in range(1, len(candidate_tag_index) + 1):
        #     all_combinations = list(itertools.combinations(candidate_tag_index, sample_size))
        #     for additional_tags in all_combinations:
        #         files = os.listdir(os.path.join('files', str(planning_task_id), 'hitting'))
        #         if str(iteration + num_workers_hitting) + '.txt' in files:
        #             return
        #         if additional_tags in blocked_hitting_sets:
        #             continue
        #         this_round_hitting_sets_num += 1
        #         branch_hitting_set = previous_root_hitting_set | set(additional_tags)
        #         hitting_set = list(branch_hitting_set)
        #         hitting_set.sort()
        #         blocked_hitting_sets.append(hitting_set)
        #         res = check_existed_hitting_set(hitting_set, planning_task_id, iteration)
        #         if len(res) != 0:
        #             this_round_existed_num += 1
        #             for subtask_id in res:
        #                 existed_task_ids.append(subtask_id)
        #             hitting_task.existed_task_ids = str(existed_task_ids)
        #             retry_delay = 0.1
        #             while True:
        #                 try:
        #                     hitting_task.save(update_fields=['existed_task_ids'],
        #                                       force_update=True)
        #                     break
        #                 except OperationalError as e:
        #                     print('search_hitting_sets 5', e)
        #                     time.sleep(retry_delay)
        #                     retry_delay *= 1 + random.random() * 0.5
        #                     continue
        #         priority = compute_priority(hitting_set, contexts, probabilistic_tag_generator)
        #         hitting_set_info = (hitting_set, priority)
        #         add_worker_task(hitting_set_info, domain_dir_path, instance_name, iteration, instance_dir_path, problem,
        #                         this_round_merged_problems, probabilistic_tag_generator, all_projected_problems, contexts,
        #                         planning_task, domain_name, planner, search_engine)
        #         if this_round_hitting_sets_num % num_workers_planning * 3 == 0:
        #             time.sleep(1)

    # hitting_task.status = 3
    # retry_delay = 0.1
    # while True:
    #     try:
    #         hitting_task.save(update_fields=['status'], force_update=True)
    #         print('hitting search finished for iteration', iteration)
    #         break
    #     except OperationalError as e:
    #         print('search_hitting_sets 4', e)
    #         time.sleep(retry_delay)
    #         retry_delay *= 1 + random.random() * 0.5
    #         continue
    # with open(os.path.join('files', str(planning_task_id), 'hitting_finished', str(iteration) + '.txt'), 'w') as f:
    #     f.write(str(iteration))
    # return


def check_not_redundant(blocked_sets, new_set):
    '''
    因为这个方法会产生类似于{0,3}, {3}的多余的set（因为{3}是{0,3}的子集），需要筛一遍
    '''
    for blocked in blocked_sets:
        intersect = blocked & new_set
        if intersect == new_set:
            return False
    return True

def incremental_tags_set():
    pass

def add_worker_task(hitting_sets_info, domain_dir_path, instance_name, iteration, instance_dir_path, problem, this_round_merged_problems, probabilistic_tag_generator, all_projected_problems, contexts, planning_task, domain_name, planner, search_engine):
    hitting_set = hitting_sets_info[0]
    priority = hitting_sets_info[1]
    time_index = time.time()
    classical_domain_path = os.path.join(domain_dir_path, 'temp',
                                         instance_name + str(iteration) + '-' + str(time_index))
    classical_instance_path = os.path.join(instance_dir_path, 'temp',
                                           instance_name + str(iteration) + '-' + str(time_index))
    write_classical_instance_file_by_hitting_set(problem, classical_instance_path, this_round_merged_problems,
                                                 probabilistic_tag_generator, hitting_set,
                                                 all_projected_problems,
                                                 contexts)
    write_classical_domain_file_by_hitting_set(problem, classical_domain_path, contexts, hitting_set,
                                               probabilistic_tag_generator, all_projected_problems)
    sub_task = WorkerTask(task=planning_task, iteration=iteration,
                          classical_domain_name=domain_name,
                          classical_instance_name=instance_name, weight=priority, status=1,
                          hitting_set_index=str(hitting_set),
                          classical_domain_path=os.path.join('pCPCES',
                                                             classical_domain_path[7:]),
                          classical_instance_path=os.path.join('pCPCES',
                                                               classical_instance_path[7:]),
                          planner=planner, search_engine=search_engine)
    # print(hitting_set)
    # print(priority)
    retry_delay = 0.1
    while True:
        try:
            sub_task.save(force_insert=True)
            break
        except OperationalError as e:
            print('search_hitting_sets 5', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    with open(os.path.join('files', str(planning_task.id), 'planning', str(iteration)+'-'+str(sub_task.id)+'.txt'), 'w') as f:
        f.write(str(iteration)+'-'+str(sub_task.id))

def get_tag_distance(tag, context):
    res = 0
    for predicate in tag:
        if predicate in context.highest_distance_contexts.keys():
            highest_distance = context.highest_distance_contexts[predicate]
            res += highest_distance
    return res

def compute_priority(hitting_set, context, probabilistic_tag_generator):
    return 10000 - len(hitting_set)
    # res = 0
    # for index in hitting_set:
    #     tag = probabilistic_tag_generator.index_tag_map[index]
    #     priority = get_tag_distance(tag, context)
    #     res += priority
    # return res

# def cancel_old_existed_tasks(planning_task, current_iteration):
#     '''
#     所有的task都在hitting里面加入队列，如果曾经出现过的也在本轮新的hitting set里面，则把老的task（还处于waiting状态的）取消掉，不用再重复计算
#     不过其实不取消也行，可能运行更快。这里持续观察
#     '''
#     # 检查还处于waiting状态的task
#     retry_delay = 0.1
#     while True:
#         try:
#             hitting_tasks = HittingTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(iteration=current_iteration))
#             if len(hitting_tasks) != 0:
#                 hitting_task = hitting_tasks[0]
#                 existed_task_ids = hitting_task.existed_task_ids
#                 existed_task_ids = eval(existed_task_ids)
#                 break
#         except OperationalError as e:
#             print('update_priority 1', e)
#             time.sleep(retry_delay)
#             retry_delay *= 1 + random.random() * 0.5
#             continue
#     retry_delay = 0.1
#     while True:
#         try:
#             waiting_worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(
#                 Q(id__in=list(existed_task_ids)) & Q(status=1))
#             num_waiting_worker_tasks = len(waiting_worker_tasks)
#             break
#         except OperationalError as e:
#             print('update_priority 2', e)
#             time.sleep(retry_delay)
#             retry_delay *= 1 + random.random() * 0.5
#             continue
#     if num_waiting_worker_tasks != 0:
#         # 将waiting状态的task取消
#         for worker_task in waiting_worker_tasks:
#             worker_task.status = 5
#             retry_delay = 0.1
#             while True:
#                 try:
#                     worker_task.save(update_fields=['status'], force_update=True)
#                     break
#                 except OperationalError as e:
#                     print('update_priority 3', e)
#                     time.sleep(retry_delay)
#                     retry_delay *= 1 + random.random() * 0.5
#                     continue


# def update_priority(planning_task, current_iteration, num_workers, problem, contexts, probabilistic_tag_generator, all_projected_problems, domain_dir_path, instance_dir_path, instance_name, each_round_merged_problems):
#     '''
#     在可以重复使用以前planning结果的时候，需要把以前的task priority提高，同时若本轮没有一个进入搜索状态，则需要杀死已经开始的任务
#     '''
#     # 检查还处于waiting状态的task
#     retry_delay = 0.1
#     while True:
#         try:
#             hitting_tasks = HittingTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(iteration=current_iteration))
#             if len(hitting_tasks) != 0:
#                 hitting_task = hitting_tasks[0]
#                 existed_task_ids = hitting_task.existed_task_ids
#                 existed_task_ids = eval(existed_task_ids)
#                 break
#         except OperationalError as e:
#             print('update_priority 1', e)
#             time.sleep(retry_delay)
#             retry_delay *= 1 + random.random() * 0.5
#             continue
#     retry_delay = 0.1
#     while True:
#         try:
#             waiting_worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id__in=list(existed_task_ids)) & Q(status=1))
#             num_waiting_worker_tasks = len(waiting_worker_tasks)
#             break
#         except OperationalError as e:
#             print('update_priority 2', e)
#             time.sleep(retry_delay)
#             retry_delay *= 1 + random.random() * 0.5
#             continue
#
#     if num_waiting_worker_tasks != 0:
#         # 将waiting状态的task提高priority
#         for worker_task in waiting_worker_tasks:
#             old_iteration = worker_task.iteration
#             hitting_set_index = worker_task.hitting_set_index
#             # 将新的加进queue，不要的记录在案
#             time_index = time.time()
#             classical_domain_path = os.path.join(domain_dir_path, 'temp',
#                                                  instance_name + str(current_iteration) + '-' + str(time_index))
#             classical_instance_path = os.path.join(instance_dir_path, 'temp',
#                                                    instance_name + str(current_iteration) + '-' + str(time_index))
#             merged_problems = each_round_merged_problems[old_iteration]
#             write_classical_instance_file_by_hitting_set(problem, classical_instance_path, merged_problems,
#                                                          probabilistic_tag_generator,
#                                                          eval(worker_task.hitting_set_index),
#                                                          all_projected_problems,
#                                                          contexts)
#             write_classical_domain_file_by_hitting_set(problem, classical_domain_path, contexts,
#                                                        eval(worker_task.hitting_set_index),
#                                                        probabilistic_tag_generator, all_projected_problems)
#             task_id = worker_task.id
#             retry_delay = 0.1
#             while True:
#                 try:
#                     worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id=task_id))
#                     if len(worker_tasks) != 0:
#                         worker_task = worker_tasks[0]
#                         break
#                 except OperationalError as e:
#                     print('update_priority 3', e)
#                     time.sleep(retry_delay)
#                     retry_delay *= 1 + random.random() * 0.5
#                     continue
#             worker_task.status = 1
#             worker_task.weight = 10000 - (10000 - worker_task.weight) * 2  - current_iteration * 2
#             worker_task.iteration = current_iteration
#             worker_task.classical_domain_path = classical_domain_path
#             worker_task.classical_instance_path = classical_instance_path
#             worker_task.applied = False
#             retry_delay = 0.1
#             while True:
#                 try:
#                     worker_task.save(update_fields=['status', 'weight', 'iteration', 'classical_domain_path', 'classical_instance_path', 'applied'], force_update=True)
#                     break
#                 except OperationalError as e:
#                     print('update_priority 4', e)
#                     time.sleep(retry_delay)
#                     retry_delay *= 1 + random.random() * 0.5
#                     continue


def push_planning_tasks_to_work(current_iteration, planning_task, num_workers, existed_task_ids):
    should_work = max(num_workers - 5, 0)
    num_this_round_waiting_tasks = len(find_files(os.path.join('files', str(planning_task.id), 'planning'), str(current_iteration)+'-*.txt'))
    num_total_is_planning = len(os.listdir(os.path.join('files', str(planning_task.id), 'is_planning')))
    num_this_round_working_tasks = len(find_files(os.path.join('files', str(planning_task.id), 'is_planning'), str(current_iteration)+'-*.txt'))
    num_previous_working_tasks = num_total_is_planning - num_this_round_working_tasks
    # 查询本轮未运行的tasks
    # retry_delay = 0.1
    # while True:
    #     try:
    #         this_round_waiting_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(iteration=current_iteration) & Q(status=1))
    #         num_this_round_waiting_tasks = len(this_round_waiting_tasks)
    #         break
    #     except OperationalError as e:
    #         print('push_planning_tasks_to_work 1', e)
    #         time.sleep(retry_delay)
    #         retry_delay *= 1 + random.random() * 0.5
    #         continue
    # 查询"非本轮"正在运行的tasks
    # retry_delay = 0.1
    # while True:
    #     try:
    #         previous_working_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(
    #             Q(task=planning_task) & Q(iteration__lt=current_iteration) & Q(status=2) & Q(plan__isnull=True)).order_by(
    #             '-weight')
    #         num_previous_working_tasks = len(previous_working_tasks)
    #         break
    #     except OperationalError as e:
    #         print('push_planning_tasks_to_work 2', e)
    #         time.sleep(retry_delay)
    #         retry_delay *= 1 + random.random() * 0.5
    #         continue
    # 查询本轮正在运行的tasks
    # retry_delay = 0.1
    # while True:
    #     try:
    #         this_round_working_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(iteration=current_iteration) & Q(status=2) & Q(plan__isnull=True))
    #         num_this_round_working_tasks = len(this_round_working_tasks)
    #         break
    #     except OperationalError as e:
    #         print('push_planning_tasks_to_work 3', e)
    #         time.sleep(retry_delay)
    #         retry_delay *= 1 + random.random() * 0.5
    #         continue
    # should_work = math.floor(num_workers)
    if num_previous_working_tasks <= should_work:
        return True
    elif num_this_round_waiting_tasks > 0 and num_workers == num_previous_working_tasks + num_this_round_working_tasks:
        if min(num_previous_working_tasks - should_work, num_this_round_waiting_tasks) > 0:
            # print('本轮task数量未达标!')
            # 查询"非本轮"正在运行的tasks,且有了planner pid
            retry_delay = 0.1
            while True:
                try:
                    previous_working_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(
                        Q(task=planning_task) & Q(iteration__lt=current_iteration) & Q(status=2) & Q(
                            plan__isnull=True) & Q(planner_pid__isnull=False) & ~Q(id__in=existed_task_ids)).order_by(
                        '-weight')
                    num_previous_working_tasks = len(previous_working_tasks)
                    break
                except OperationalError as e:
                    print('push_planning_tasks_to_work 4', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            kill_index = 0
            while kill_index < min(num_previous_working_tasks - should_work, num_this_round_waiting_tasks):
                task = previous_working_tasks[kill_index]
                task_pid = task.pid
                planner_pid = task.planner_pid
                task_status = process_status(task_pid)
                # print('planning', task_status)
                # if (task_status == 'Running' or task_status == 'Sleeping' or task_status == 'Disk_Sleep') and task.status == 2:
                #     os.kill(task_pid, signal.SIGTERM)
                if planner_pid != 'null' and planner_pid is not None and os.path.exists(os.path.join('files', str(planning_task.id), 'is_planning',
                                               str(task.iteration) + '-' + str(task.id) + '.txt')):
                    planner_status = process_status(planner_pid)
                    if planner_status == 'Running' or planner_status == 'Sleeping':
                        try:
                            os.kill(planner_pid, signal.SIGTERM)  # 发送 SIGTERM 信号
                        except OSError as e:
                            print("发生 OSError:", e)
                        os.remove(os.path.join('files', str(planning_task.id), 'is_planning',
                                               str(task.iteration) + '-' + str(task.id) + '.txt'))
                        with open(os.path.join('files', str(planning_task.id), 'planning', str(task.iteration)+'-'+str(task.id)+'.txt'), 'w')as f:
                            f.write(str(task.iteration)+'-'+str(task.id))
                kill_index += 1
    return False

def push_hitting_task_to_work(planning_task, current_iteration, num_hitting_worker):
    retry_delay = 0.1
    while True:
        try:
            previous_working_tasks = HittingTask.objects.select_for_update(nowait=True).filter(
                Q(task=planning_task) & Q(iteration=current_iteration-num_hitting_worker) & Q(status=2))
            num_previous_working_tasks = len(previous_working_tasks)
            break
        except OperationalError as e:
            print('push_hitting_task_to_work 1', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    if num_previous_working_tasks != 0:
        while True:
            try:
                selected_task = previous_working_tasks.first()
                break
            except OperationalError as e:
                print('push_hitting_task_to_work 2', e)
                time.sleep(retry_delay)
                retry_delay *= 1 + random.random() * 0.5
                continue
        task_pid = selected_task.pid
        hitter_pid = selected_task.hitter_pid
        task_status = process_status(task_pid)
        print('hitting', task_status)
        # if (task_status == 'Running' or task_status == 'Sleeping' or task_status=='Disk_Sleep') and selected_task.status == 2:
        #     os.kill(task_pid, signal.SIGTERM)
        if hitter_pid != 'null' and hitter_pid is not None:
            phitter_status = process_status(hitter_pid)
            if phitter_status == 'Running' or phitter_status == 'Sleeping':
                try:
                    os.kill(hitter_pid, signal.SIGTERM)  # 发送 SIGTERM 信号
                    print('kill hitting task of iteration', selected_task.iteration)
                    with open(os.path.join('files', str(planning_task.id), 'hitting_finished', str(selected_task.iteration) + '.txt'), 'w') as f:
                        f.write(str(selected_task.iteration))
                except OSError as e:
                    print("发生 OSError:", e)



def all_subtasks_finished(planning_task, iteration):
    retry_delay = 0.1
    while True:
        try:
            hitting_tasks = HittingTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(iteration=iteration))
            if (hitting_tasks) != 0:
                hitting_task = hitting_tasks[0]
                existed_task_ids = hitting_task.existed_task_ids
                existed_task_ids = eval(existed_task_ids)
                num_existed_task_ids = len(existed_task_ids)
                break
        except OperationalError as e:
            print('all_subtasks_finished 1', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    retry_delay = 0.1
    while True:
        try:
            worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id__in=existed_task_ids) & (Q(status=3)|Q(status=4)))
            num_worker_tasks = len(worker_tasks)
            break
        except OperationalError as e:
            print('all_subtasks_finished 2', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    if num_worker_tasks != num_existed_task_ids:
        return False
    else:
        return True

def check_existed_hitting_set(hitting_set, planning_task_id, current_iteration):
    '''
    如果这轮hitting set里面有曾经完成过的task，那就直接跳过本轮
    '''
    subtask_id_set = set()
    retry_delay = 0.1
    while True:
        try:
            planning_tasks = Task.objects.select_for_update(nowait=True).filter(Q(id=planning_task_id))
            if len(planning_tasks) != 0:
                planning_task = planning_tasks[0]
                break
        except OperationalError as e:
            print('check_existed_hitting_set 1', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    retry_delay = 0.1
    while True:
        try:
            worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(iteration__lt=current_iteration) & Q(hitting_set_index=str(hitting_set)) & (Q(status=1)|Q(status=2)|Q(status=3)|Q(status=4))).values('id')
            num_worker_tasks = len(worker_tasks)
            break
        except OperationalError as e:
            print('check_existed_hitting_set 2', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    if num_worker_tasks != 0:
        for worker in worker_tasks:
            sub_task_id = worker['id']
            subtask_id_set.add(sub_task_id)
    return subtask_id_set

def get_candidate_plan_from_database(planning_task, iteration, existed_task_ids):
    # TODO:取哪一个
    # 检查task没有plan
    # retry_delay = 0.1
    # while True:
    #     try:
    #         existed_task_ids = HittingTask.objects.select_for_update(nowait=True).get(Q(task=planning_task) & Q(iteration=iteration)).existed_task_ids
    #         existed_task_ids = eval(existed_task_ids)
    #         break
    #     except OperationalError as e:
    #         print('get_candidate_plan_from_database 1', e)
    #         time.sleep(retry_delay)
    #         retry_delay *= 1 + random.random() * 0.5
    #         continue
    retry_delay = 0.1
    while True:
        try:
            worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id__in=existed_task_ids) & Q(plan__isnull=False) & (Q(status=3)|Q(status=4)))
            num_worker_tasks = len(worker_tasks)
            break
        except OperationalError as e:
            print('get_candidate_plan_from_database 2', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    if num_worker_tasks != 0:
        retry_delay = 0.1
        while True:
            try:
                worker_task = worker_tasks.first()
                candidate_plan = worker_task.plan
                return candidate_plan, worker_task, worker_task.status
            except OperationalError as e:
                print('get_candidate_plan_from_database 3', e)
                time.sleep(retry_delay)
                retry_delay *= 1 + random.random() * 0.5
                continue
    return None, None, None

def check_final_plan(planning_task):
    retry_delay = 0.1
    while True:
        try:
            worker_task = WorkerTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(has_sample_tags=False))
            num_worker_task = len(worker_task)
            break
        except OperationalError as e:
            print('check_final_plan 1', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    if num_worker_task != 0:
        retry_delay = 0.1
        while True:
            try:
                worker_task = worker_task.first() # TODO:which one
                return worker_task
            except OperationalError as e:
                print('check_final_plan 2', e)
                time.sleep(retry_delay)
                retry_delay *= 1 + random.random() * 0.5
                continue
    else:
        return None

def kill_all_processings():
    time.sleep(5)
    process1 = subprocess.Popen(['killall', 'ff'])
    process2 = subprocess.Popen(['killall', 'python3'])
    time.sleep(5)
    return

def count_finished_planning_tasks(planning_task):
    retry_delay = 0.1
    while True:
        try:
            worker_task = WorkerTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & (Q(status=3)|Q(status=4)))
            num_worker_task = len(worker_task)
            return num_worker_task
        except OperationalError as e:
            print('count_finished_planning_tasks', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue

def process_status(pid):
    try:
        process = psutil.Process(pid)
        status = process.status()
        if status == psutil.STATUS_RUNNING:
            return "Running"
        elif status == psutil.STATUS_SLEEPING:
            return "Sleeping"
        elif status == psutil.STATUS_STOPPED:
            return "Stopped"
        elif status == psutil.STATUS_ZOMBIE:
            return "Zombie"
        elif status == psutil.STATUS_DEAD:
            return "Dead"
        elif status == psutil.STATUS_IDLE:
            return "Idle"
        elif status == psutil.STATUS_DISK_SLEEP:
            return "Disk_Sleep"
        else:
            return "Unknown"
    except psutil.NoSuchProcess:
        return "No such process"
    except psutil.AccessDenied:
        return "Access denied"
    except Exception as e:
        return f"Error: {e}"


def conformant_probabilistic_planning(domain, instance, planner, num_workers_planning, num_workers_hitting, num_workers_tags, hitting_batch_size, hitting_search_method, incremental_tags, search_engine='eager(single(ff()))'):
    num_skip = 0
    total_time_start = time.time()
    problem = open_pddl(domain, instance, type='conformant_probabilistic_planning')
    candidate_plan = None
    domain_dir_path = os.path.dirname(domain)
    instance_dir_path = os.path.dirname(instance)
    if not os.path.exists(os.path.join(domain_dir_path, 'temp')):
        os.makedirs(os.path.join(domain_dir_path, 'temp'))
    if not os.path.exists(os.path.join(instance_dir_path, 'temp')):
        os.makedirs(os.path.join(instance_dir_path, 'temp'))
    domain_name = os.path.basename(domain)
    instance_name = os.path.basename(instance)
    threshold = problem.threshold
    temp = problem.init
    problem.init = problem.all_possible_initial
    relaxed_reachable, atoms, actions, axioms, reachable_action = explore_probabilistic(problem)
    problem.init = temp
    print('start computing contexts')
    context_time_start = time.time()
    contexts = Context(atoms, actions, problem.goal,
                       problem.all_possible_initial - problem.initial_true - problem.initial_false, True)
    print('contexts computing completed')
    print('contexts computing time:', time.time() - context_time_start)
    action_map = get_action_map(actions, dict())

    planning_task = Task(domain_name=domain_name, instance_name=instance_name, probability_threshold=problem.threshold,
                         status=2, domain_path=domain, instance_path=instance)
    retry_delay = 0.1
    while True:
        try:
            planning_task.save(force_insert=True)
            break
        except OperationalError as e:
            print('planning task', e)
            time.sleep(retry_delay)
            retry_delay *= 1 + random.random() * 0.5
            continue
    planning_task_id = planning_task.id
    print('planning task id', planning_task_id)


    iteration = 1
    all_projected_problems = AllProjectedProblems(problem, contexts)
    probabilistic_tag_generator = TagGenerator(problem, candidate_plan, action_map, contexts)
    print('start computing tags')
    tags_time_start = time.time()
    probabilistic_tag_generator.find_all_tags()
    print('tags computing completed')
    print('tags computing time:', time.time() - tags_time_start)
    monitorPlanningProcessing = multiprocessing.Process(target=monitor_planning_processing,
                                                        args=(num_workers_planning, planning_task))
    monitorHittingProcessing = multiprocessing.Process(target=monitor_hitting_processing,
                                                       args=(problem, planning_task, num_workers_hitting, num_workers_planning,
                                                             hitting_batch_size, hitting_search_method, incremental_tags,
                                                             planning_task_id,
                                                             domain_dir_path,
                                                             instance_name,
                                                             instance_dir_path,
                                                             probabilistic_tag_generator,
                                                             all_projected_problems,
                                                             contexts, domain_name, planner,
                                                             search_engine
                                                             ))
    monitorNormalSampleTagProcessing = multiprocessing.Process(target=monitor_normal_sample_tags_processing,
                                                        args=(problem, num_workers_tags, planning_task, action_map, contexts, probabilistic_tag_generator, all_projected_problems, total_time_start, threshold))
    monitorFirstPrioritySampleTagProcessing = multiprocessing.Process(target=monitor_first_priority_sample_tags_processing,
                                                               args=(
                                                               problem, num_workers_tags, planning_task, action_map,
                                                               contexts, probabilistic_tag_generator,
                                                               all_projected_problems, total_time_start, threshold))

    if not os.path.exists('files'):
        os.mkdir('files')
    if not os.path.exists(os.path.join('files', str(planning_task_id))):
        os.mkdir(os.path.join('files', str(planning_task_id)))
    hitting_file_path = os.path.join('files', str(planning_task_id), 'hitting')
    hitting_finished_file_path = os.path.join('files', str(planning_task_id), 'hitting_finished')
    planning_file_path = os.path.join('files', str(planning_task_id), 'planning')
    is_planning_file_path = os.path.join('files', str(planning_task_id), 'is_planning')
    planning_finished_file_path = os.path.join('files', str(planning_task_id), 'planning_finished')
    has_plan_file_path = os.path.join('files', str(planning_task_id), 'has_plan')
    tag_finished_file_path = os.path.join('files', str(planning_task_id), 'tag_finished')


    if not os.path.exists(hitting_file_path):
        os.mkdir(hitting_file_path)
    if not os.path.exists(hitting_finished_file_path):
        os.mkdir(hitting_finished_file_path)
    if not os.path.exists(planning_file_path):
        os.mkdir(planning_file_path)
    if not os.path.exists(planning_finished_file_path):
        os.mkdir(planning_finished_file_path)
    if not os.path.exists(is_planning_file_path):
        os.mkdir(is_planning_file_path)
    if not os.path.exists(has_plan_file_path):
        os.mkdir(has_plan_file_path)
    if not os.path.exists(tag_finished_file_path):
        os.mkdir(tag_finished_file_path)

    monitorHittingProcessing.start()
    monitorFirstPrioritySampleTagProcessing.start()
    if num_workers_tags > 1:
        monitorNormalSampleTagProcessing.start()
    monitorPlanningProcessing.start()
    existed_task_ids = None
    while True:
        print('iteration:', iteration)
        has_sample_tags = True
        if iteration == 1:
            # 第一轮candidate plan为null，找到第一次的sample tags
            first_worker_task = WorkerTask(task=planning_task, iteration=0,
                       classical_domain_name=domain_name,
                       classical_instance_name=instance_name, weight=10000, status=3,
                       hitting_set_index='[]',
                       classical_domain_path='Null',
                       classical_instance_path='Null',
                       plan='[]', first_priority=0,
                       planner=planner, search_engine=search_engine)
            retry_delay = 0.1
            while True:
                try:
                    first_worker_task.save(force_insert=True)
                    break
                except OperationalError as e:
                    print('conformant_probabilistic_planning 1', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            with open(os.path.join('files', str(planning_task_id), 'has_plan',
                                   str(first_worker_task.iteration) + '-' + str(first_worker_task.id) + '.txt'), 'w') as f:
                f.write(str(first_worker_task.iteration) + '-' + str(first_worker_task.id))
            # selected_worker_task_id = first_worker_task.id

        continue_monitor = True
        while continue_monitor:
            files = os.listdir(os.path.join('files', str(planning_task_id), 'tag_finished'))
            for file in files:
                file = file.split('.')[0]
                filename = file.split('_')
                file_iteration = int(filename[0])
                worker_id = int(filename[1])
                if (existed_task_ids is not None and len(existed_task_ids) > 0 and worker_id in existed_task_ids) or (file_iteration == iteration - 1):
                    retry_delay = 0.1
                    while True:
                        try:
                            finished_worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(
                                Q(id=worker_id))
                            num_finished_worker_tasks = len(finished_worker_tasks)
                            break
                        except OperationalError as e:
                            print('conformant_probabilistic_planning 2', e)
                            time.sleep(retry_delay)
                            retry_delay *= 1 + random.random() * 0.5
                            continue
                    if num_finished_worker_tasks > 0:
                        selected_worker = finished_worker_tasks[0]
                        continue_monitor = False
                        break

        has_sample_tags = selected_worker.has_sample_tags
        if has_sample_tags:
            candidate_plan = selected_worker.plan
            probability = selected_worker.tags_probability
            sample_tag_index = eval(selected_worker.sample_tag_index)
            used_projected_problems = eval(selected_worker.used_projected_problems)
            # print('selected worker task id', selected_worker.id)
            # print('candidate plan', candidate_plan)
            sample_tags_history = eval(planning_task.sample_tags_history)
            # print('sample_tags_history', sample_tags_history)
            sample_tags_history.append(sample_tag_index)
            planning_task.sample_tags_history = json.dumps(sample_tags_history)
            retry_delay = 0.1
            while True:
                try:
                    planning_task.save(update_fields=['sample_tags_history'], force_update=True)
                    break
                except OperationalError as e:
                    print('conformant_probabilistic_planning 2', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
        else:
            print('find a valid plan')
            print(candidate_plan)
            print('plan length:', len(candidate_plan))
            # print('sample tag searching time:', sample_tag_searching_time)
            print('iterations:', iteration)
            break

        # push_hitting_task_to_work(planning_task, iteration, num_workers_hitting)

        print('sample tags probability', probability)
        retry_delay = 0.1
        while True:
            try:
                hitting_task = HittingTask(task=planning_task, iteration=iteration, status=1, sample_tags_history=str(sample_tags_history), used_projected_problems=str(used_projected_problems))
                hitting_task.save(force_insert=True)
                # print('hitting', iteration, 'saved')
                break
            except OperationalError as e:
                print('conformant_probabilistic_planning 2', e)
                time.sleep(retry_delay)
                retry_delay *= 1 + random.random() * 0.5
                continue
        with open(os.path.join(hitting_file_path, str(iteration) + '.txt'), 'w') as f:
            f.write(str(iteration))


        continue_searching_plan = True
        updated_priority = False
        pushed_tasks_to_work = False
        # candidate_plan = None
        printed = False
        while continue_searching_plan:  # 这个循环只要是为了防止问题无解，需要不停的拿到hitting set直到所有hitting set都检查过了才能确定没有解
            # final_plan_worker = check_final_plan(planning_task) # 只要一个candidate plan没有足够多的sample tags，就是final plan了
            # if final_plan_worker is not None:
            #     candidate_plan = final_plan_worker.plan
            #     print('find a valid plan through previous iteration', final_plan_worker.iteration)
            #     print(candidate_plan)
            #     print('plan length:', len(eval(candidate_plan.replace('\"', '\''))))
            #     # print('sample tag searching time:', sample_tag_searching_time)
            #     print('iterations:', iteration)
            #     total_time = time.time() - total_time_start
            #     finished_num_planning_tasks = count_finished_planning_tasks(planning_task)
            #     print('total time:', total_time)
            #     print('num planning tasks finished:', finished_num_planning_tasks)
            #     print('num skip:', num_skip)
            #     kill_all_processings()
            #     print('')
            #     return
            retry_delay = 0.1
            while True:
                try:
                    selected_hitting = HittingTask.objects.select_for_update(nowait=True).filter(Q(task=planning_task) & Q(iteration=iteration))
                    if len(selected_hitting) != 0:
                        existed_task_ids = selected_hitting[0].existed_task_ids
                        existed_task_ids = eval(existed_task_ids)
                        num_existed_task_ids = len(existed_task_ids)
                        break
                except OperationalError as e:
                    print('conformant_probabilistic_planning 3', e)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue

            if num_existed_task_ids != 0:
                # 先取消掉以前出现过相同hitting set且还处于waiting状态的任务
                # cancel_old_existed_tasks(planning_task, iteration)
                if not printed:
                    print('可以使用曾经的task结果')
                    printed = True
                # # 只要一个candidate plan没有足够多的sample tags，就是final plan了
                # final_plan_worker = check_final_plan(
                #     planning_task)
                # if final_plan_worker is not None:
                #     candidate_plan = final_plan_worker.plan
                #     print('find a valid plan through previous iteration', final_plan_worker.iteration)
                #     print(candidate_plan)
                #     print('plan length:', len(eval(candidate_plan.replace('\"', '\''))))
                #     # print('sample tag searching time:', sample_tag_searching_time)
                #     print('iterations:', iteration)
                #     total_time = time.time() - total_time_start
                #     print('total time:', total_time)
                #     kill_all_processings()
                #     time.sleep(5)
                #     print('')
                #     return
                # Case1: 若所有任务都已经结束了
                candidate_plan, worker, selected_worker_status = get_candidate_plan_from_database(planning_task,
                                                                                                  iteration,
                                                                                                  existed_task_ids)
                # Case1: 所有任务已完成，没有plan或者有plan
                # Case2: 还有任务未完成，但是已经完成的任务里面有plan存在了
                if candidate_plan is not None:
                    candidate_plan = eval(candidate_plan)
                    continue_searching_plan = False
                    if selected_worker_status == 3:
                        update_first_priority(worker)
                    num_skip += 1
                # all_finished = all_subtasks_finished(planning_task, iteration)
                # if all_finished:
                #     # Case1: 所有任务已完成，没有plan或者有plan
                #     print('Case1.1: 所有任务已完成')
                #     candidate_plan, worker, selected_worker_status = get_candidate_plan_from_database(planning_task, iteration, existed_task_ids)
                #     if candidate_plan is not None:
                #         candidate_plan = eval(candidate_plan)
                #         continue_searching_plan = False
                #         if selected_worker_status == 3:
                #             update_first_priority(worker)
                #         num_skip += 1
                #     # break
                # else:
                #     candidate_plan, worker, selected_worker_status = get_candidate_plan_from_database(planning_task, iteration, existed_task_ids)
                #     if candidate_plan is not None:
                #         # Case2: 还有任务未完成，但是已经完成的任务里面有plan存在了
                #         print('Case2: 还有任务未完成，但是已经完成的任务里面有plan存在了')
                #         candidate_plan = eval(candidate_plan)
                #         continue_searching_plan = False
                #         if selected_worker_status == 3:
                #             update_first_priority(worker)
                #         num_skip += 1
                        # break
                    # else:
                        # Case3: 还有任务未完成，且目前为止还没发现一个plan
                        # 把当前发现的task提前
                        # print('Case3: 还有任务未完成，且目前为止还没发现一个plan', updated_priority)
                        # if not updated_priority:
                        #     update_priority(planning_task, iteration, num_workers_planning, problem, contexts, probabilistic_tag_generator, all_projected_problems, domain_dir_path, instance_dir_path, instance_name, each_round_merged_problems)
                        #     updated_priority = True

            if continue_searching_plan:
                # print('正常程序')
                # case1. 不能skip，正常程序
                # case2. 可以skip，但是都没找到plan，进入正常程序
                # hitting_status = hitting_task.status
                # hitting_num = hitting_task.this_round_hitting_sets_num
                # if hitting_num == 0 and hitting_status == 3:  # 搜寻hitting set已结束但是没有hitting set
                #     print("no solution due to no hitting set")
                #     # print('sample tag searching time:', sample_tag_searching_time)
                #     print('iterations:', iteration)
                #     total_time = time.time() - total_time_start
                #     print('total time:', total_time)
                #     kill_all_processings()
                #     print('')
                #     return

                # if not pushed_tasks_to_work:
                #     # 这里查询本轮task是否进入工作状态，如果没有，则杀死上一轮中的一个任务
                #     pushed_tasks_to_work = push_planning_tasks_to_work(iteration, planning_task, num_workers_planning, existed_task_ids)
                # 监控本轮worker的工作情况，一旦有一个完成且有plan，则可以进入下一轮。
                result = round_monitor(iteration, planning_task)
                if result == "Continue searching":
                    continue
                elif result == "No candidate plan":
                    candidate_plan = None
                    break
                else:
                    # 找到了一个plan
                    # retry_delay = 0.1
                    # while True:
                    #      try:
                    #         selected_worker = WorkerTask.objects.select_for_update(nowait=True).get(id=result)
                    #         break
                    #      except OperationalError as e:
                    #         print('conformant_probabilistic_planning 4', e)
                    #         time.sleep(retry_delay)
                    #         retry_delay *= 1 + random.random() * 0.5
                    #         continue
                    candidate_plan = eval(result.plan)
                    # selected_worker_task_id = result.id
                    update_first_priority(result)
                    break

        if candidate_plan is None:
            print("no solution due to no candidate plan")
            # print('sample tag searching time:', sample_tag_searching_time)
            print('iterations:', iteration)
            break
        else:
            print('find a plan')
            print('number of skip until now', num_skip)
            print('')

        # if iteration == 17:
        #     print('finished')
        #     kill_all_processings()
        #     return
        iteration += 1
    total_time = time.time() - total_time_start
    print('total time:', total_time)
    finished_num_planning_tasks = count_finished_planning_tasks(planning_task)
    print('num planning tasks finished:', finished_num_planning_tasks)
    print('num skip:', num_skip)
    kill_all_processings()
    print('')
    return

def run(domain, instance, num_workers_planning, num_workers_hitting, num_workers_tags, method, planner='ff'):
    conformant_probabilistic_planning(domain, instance, planner, num_workers_planning=num_workers_planning, num_workers_hitting=num_workers_hitting, num_workers_tags=num_workers_tags, hitting_batch_size=1, hitting_search_method=method, incremental_tags=False)
    return


    # parser = argparse.ArgumentParser()
    # parser.add_argument('-p', '--planning', dest='planning')
    # parser.add_argument('-t', '--tag', dest='tag')
    # parser.add_argument('-d', '--domain', dest='domain')
    # parser.add_argument('-i', '--instance', dest='instance')
    # parser.add_argument('-p', '--planner', dest='planner', default='ff')
    # parser.add_argument('-s', '--search_engine', dest='search_engine', default='eager(single(ff))')
    # parser.add_argument('-hs', '--hitting_set', dest='hitting_set', default=False)
    # parser.add_argument('-ht', '--hitting_type', dest='hitting_type', default='random')
    # args = parser.parse_args()
    # print(args.planning)
    # print(args.tag)
    # conformant_probabilistic_planning('pCPCES/FD-Benchmarks-0.75/dispose/domain.pddl', 'pCPCES/FD-Benchmarks-0.75/dispose/instances/p_8_1.pddl', 'ff', num_workers_planning=args.planning, num_workers_hitting=2, num_workers_tags=args.tag, hitting_batch_size=1, hitting_search_method='kissat', incremental_tags=False)


    # print(args.planner)
    # print(args.search_engine)
    # print(args.hitting_set)
    # print(args.hitting_type)
    # conformant_probabilistic_planning(args.domain, args.instance, args.planner, args.search_engine, args.hitting_set, args.hitting_type)

# if __name__ == '__main__':
    # run()