# -*- coding: utf-8 -*-
import sys
sys.path.append("..")

import os
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "parallel_CPCES.settings")
import django
django.setup()
from pCPCES.models import Task
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
import copy
from pysat.examples.hitman import Hitman
import psutil
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



def find_files(directory, file_pattern):
    search_path = os.path.join(directory, file_pattern)
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
                                    print('probability is greater than 1, bug!')
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
                        print('not have enough sample tag')
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
                                    print('probability is greater than 1, bug!')
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
                        print('not have enough sample tag')
                        print('find a valid plan')
                        print(candidate_plan)
                        print('plan length', len(candidate_plan))
                        total_time = time.time() - total_time_start
                        print('iteration', selected_task.iteration)
                        print('total time:', total_time)
                        kill_all_processings()



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
        constraint_object.get_projected_initial_assert()  # 不需要initial assert，但是需要initial的declare
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
    used_projected_problems = None
    sample_tag_index = None
    if sample_tags is not None:
        num_of_sample_tags, used_projected_problems, sample_tag_index = get_information_from_sample_tags_for_hitting_set(
            probabilistic_tag_generator.tag_index_map, sample_tags)
    worker.sample_tag_index = json.dumps(sample_tag_index)
    if sample_tags is not None:
        worker.has_sample_tags = True
    else:
        worker.has_sample_tags = False
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

def update_first_priority(worker_task):
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
    num_tags = len(probabilistic_tag_generator.all_tags_in_one_list)


    all_true_and_false_tags_by_index = probabilistic_tag_generator.all_true_and_false_tags_by_index
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
    print('entering hitting set computing')
    num_additional_tags_in_hitting = 0
    files = os.listdir(os.path.join('files', str(planning_task_id), 'hitting'))
    if str(iteration + num_workers_hitting) + '.txt' in files:
        return
    while True:
        if hitting_search_method == 'hitman':
            hitting_set = h.get()  # 这个函数自动实现了minimal的hitting set
        else:
            hitting_set = get_hitting_set(all_sets, num_elements, blocked_hitting_sets, iteration, hitting_task)
        num_additional_tags_in_hitting += 1
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



def check_not_redundant(blocked_sets, new_set):
    '''
    check whether the new set is the subset of any set in blocked sets
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
    check whether a hitting set in encountered depth has been shown on previous depth
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
                worker_task = worker_task.first()
                return worker_task
            except OperationalError as e:
                print('check_final_plan 2', e)
                time.sleep(retry_delay)
                retry_delay *= 1 + random.random() * 0.5
                continue
    else:
        return None

def kill_all_processings():
    process1 = subprocess.Popen(['killall', 'ff'])
    process2 = subprocess.Popen(['killall', 'python3'])
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
    while True: # main loop
        print('iteration:', iteration)
        if iteration == 1:
            # set candidate plan = null, and request the first sample tag set
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

        continue_monitor = True
        while continue_monitor: # await counter tag sets
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
            sample_tags_history = eval(planning_task.sample_tags_history)
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


        print('sample tags probability', probability)
        retry_delay = 0.1
        while True:
            try:
                hitting_task = HittingTask(task=planning_task, iteration=iteration, status=1, sample_tags_history=str(sample_tags_history), used_projected_problems=str(used_projected_problems))
                hitting_task.save(force_insert=True)
                break
            except OperationalError as e:
                print('conformant_probabilistic_planning 2', e)
                time.sleep(retry_delay)
                retry_delay *= 1 + random.random() * 0.5
                continue
        with open(os.path.join(hitting_file_path, str(iteration) + '.txt'), 'w') as f:
            f.write(str(iteration))


        continue_searching_plan = True
        while continue_searching_plan:  # inner loop
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
                # check whether the system can skip plan searching
                candidate_plan, worker, selected_worker_status = get_candidate_plan_from_database(planning_task,
                                                                                                  iteration,
                                                                                                  existed_task_ids)
                # the system can skip plan searching
                if candidate_plan is not None:
                    candidate_plan = eval(candidate_plan)
                    continue_searching_plan = False
                    if selected_worker_status == 3:
                        update_first_priority(worker)
                    num_skip += 1

            if continue_searching_plan:
                # get earliest plan status
                result = round_monitor(iteration, planning_task)
                if result == "Continue searching":
                    continue
                elif result == "No candidate plan":
                    candidate_plan = None
                    break
                else:
                    # find a plan
                    candidate_plan = eval(result.plan)
                    update_first_priority(result)
                    break

        if candidate_plan is None:
            print("no solution due to no candidate plan")
            print('iterations:', iteration)
            break
        else:
            print('find a plan')
            print('number of skip until now', num_skip)
            print('')

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
