import os
import subprocess
from pCPCES.ConformantProbabilisticPlanning.SampleTagGenerator import SampleTagsGenerator
from pCPCES.translate.pddl.conditions import Truth
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.ConformantPlanning.extract_plan import extract_ff_plan
from pCPCES.ConformantPlanning.extract_plan import extract_fd_plan
from pCPCES.ConformantPlanning.extract_plan import extract_mad_plan
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.models import WorkerTask
from django.db.models import Q
from django.db import IntegrityError
import logging
import json
import random
from django.db import OperationalError
import time


def writeClassicalSampleFile(sample_list, problem, instance_file):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        obj = str(obj).split(': ')
        res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    for i in range(1, len(sample_list) + 1):
        res += '  int' + str(i) + ' - interpretation\n'
    res += ')\n'
    res += '(:init\n'
    for i in range(1, len(sample_list) + 1):
        counter_example_set = sample_list[i - 1]
        for counter_example in counter_example_set:
            res += '  (' + counter_example + ' int' + str(i) + ')\n'
    res += ')\n'
    res += '(:goal (forall (?interpr - interpretation)'
    res += problem.goal.get_classical_problem_predicate()

    res += ')))'
    # print(res)
    with open(instance_file, 'w') as f:
        f.write(res)

def writeMergedClassicalSampleFile(sample_list, problem, instance_file, contexts):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        obj = str(obj).split(': ')
        res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    for i in range(1, len(sample_list) + 1):
        res += '  int' + str(i) + ' - interpretation\n'
    res += ')\n'
    res += '(:init\n'
    for i in range(1, len(sample_list) + 1):
        counter_example_set = sample_list[i - 1]
        for counter_example in counter_example_set:
            if counter_example.split(' ')[0] in contexts.all_predicate_name_in_contexts:
                res += '  (' + counter_example + ' int' + str(i) + ')\n'
            else:
                if i == 1:
                    res += '  (' + counter_example + ')\n'
    res += ')\n'
    res += '(:goal (forall (?interpr - interpretation)'
    res += problem.goal.get_classical_problem_predicate()

    res += ')))'
    # print(res)
    with open(instance_file, 'w') as f:
        f.write(res)

def writeMergedSeparatedClassicalSampleFile(sample_list, problem, instance_file, contexts):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        obj = str(obj).split(': ')
        res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    for i in range(1, len(sample_list) + 1):
        res += '  int' + str(i) + ' - interpretation\n'
    res += ')\n'
    res += '(:init\n'
    for i in range(1, len(sample_list) + 1):
        counter_example_set = sample_list[i - 1]
        for counter_example in counter_example_set:
            if counter_example.split(' ')[0] in contexts.all_predicate_name_in_contexts:
                res += '  (' + counter_example + ' int' + str(i) + ')\n'
            else:
                if i == 1:
                    res += '  (' + counter_example + ')\n'
    res += ')\n'
    res += '(:goal (and '
    for i in range(1, len(sample_list) + 1):
        res += problem.goal.get_merged_seperated_classical_problem_predicate(contexts, i, [])

    res += ')))'
    with open(instance_file, 'w') as f:
        f.write(res)


def writeSeparatedClassicalSampleFile(sample_list, problem, instance_file):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        obj = str(obj).split(': ')
        res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    for i in range(1, len(sample_list) + 1):
        res += '  int' + str(i) + ' - interpretation\n'
    res += ')\n'
    res += '(:init\n'
    for i in range(1, len(sample_list) + 1):
        counter_example_set = sample_list[i - 1]
        for counter_example in counter_example_set:
            res += '  (' + counter_example + ' int' + str(i) + ')\n'
    res += ')\n'
    res += '(:goal (and '
    for i in range(1, len(sample_list) + 1):
        res += problem.goal.get_separated_classical_problem_predicate(i)

    res += ')))'
    with open(instance_file, 'w') as f:
        f.write(res)


def writeClassicalSampleFileForSUPERFD(sample_list, problem, instance_file):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        if obj not in problem.constants:
            obj = str(obj).split(': ')
            res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    res += ')\n'
    res += '(:init\n'
    counter_example_set = sample_list[-1]
    for counter_example in counter_example_set:
        res += '  (' + counter_example + ')\n'
    res += ')\n'
    res += '(:goal '
    res += problem.goal.get_superfd_predicate()
    res += '))'
    with open(instance_file, 'w') as f:
        f.write(res)

def writeMergedClassicalDomainFile(problem, domain_file, contexts):
    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '(:types  '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += 'interpretation - object )\n'
    res += '(:predicates (true) '
    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            if predicate.split(' ')[0] in contexts.all_predicate_name_in_contexts:
                res += '(' + predicate + ' ?x - interpretation)'
            else:
                res += '(' + predicate + ')'
    res += ')\n'
    for action in problem.actions:
        res += '(:action ' + action.name + '\n'
        res += ':parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'
        precondition = action.precondition
        precondition_can_be_merged = predicates_can_be_merged(precondition, contexts)
        if len(action.precondition.parts) != 0 or isinstance(action.precondition, Atom) or isinstance(
                action.precondition, NegatedAtom):
            if precondition_can_be_merged:
                res += ':precondition '
                res += action.precondition.get_merged_classical_problem_predicate(contexts)
                res += '\n'
            else:
                res += ':precondition (forall (?interpr - interpretation)'
                res += action.precondition.get_merged_classical_problem_predicate(contexts)
                res += ')\n'
        res += ':effect (and '
        effect_map = dict()
        truth_effect_list = list()
        for effect in action.effects:
            if type(effect.condition) != Truth:
                condition = effect.condition
                if condition in effect_map.keys():
                    effect_map[condition].append(effect.literal)
                else:
                    effect_map[condition] = [effect.literal]
            else:
                truth_effect_list.append(effect.literal)
        for effect in truth_effect_list:
            effect_can_be_merged = predicates_can_be_merged(effect, contexts)
            if effect_can_be_merged:
                res += effect.get_merged_classical_problem_predicate(contexts)
            else:
                res += '(forall (?interpr - interpretation) '
                res += effect.get_merged_classical_problem_predicate(contexts)
                res += ')'
        if len(effect_map) != 0:
            for condition, effects in effect_map.items():
                condition_can_be_merged = predicates_can_be_merged(condition, contexts)
                effect_can_be_merged = predicates_can_be_merged(effects, contexts)
                if condition_can_be_merged and effect_can_be_merged:
                    res += '(when '
                    res += condition.get_merged_classical_problem_predicate(contexts)
                    res += Conjunction(effects).get_merged_classical_problem_predicate(contexts)
                    res += ')'
                else:
                    res += '(forall (?interpr - interpretation) '
                    res += '(when '
                    res += condition.get_merged_classical_problem_predicate(contexts)
                    res += Conjunction(effects).get_merged_classical_problem_predicate(contexts)
                    res += '))'
        res += '))\n'
    res += ')'
    with open(domain_file, 'w') as f:
        f.write(res)

def predicates_can_be_merged(item, contexts):
    if isinstance(item, Atom):
        if item.predicate in contexts.all_predicate_name_in_contexts:
            return False
    elif isinstance(item, NegatedAtom):
        if item.negate().predicate in contexts.all_predicate_name_in_contexts:
            return False
    else:
        if isinstance(item, list):
            for i in item:
                if isinstance(i, Atom):
                    if i.predicate in contexts.all_predicate_name_in_contexts:
                        return False
                elif isinstance(i, NegatedAtom):
                    if i.negate().predicate in contexts.all_predicate_name_in_contexts:
                        return False
        else:
            for i in item.parts:
                if isinstance(i, Atom):
                    if i.predicate in contexts.all_predicate_name_in_contexts:
                        return False
                elif isinstance(i, NegatedAtom):
                    if i.negate().predicate in contexts.all_predicate_name_in_contexts:
                        return False
    return True


def writeMergedSeparatedClassicalDomainFile(problem, domain_file, contexts, sample_list=None):
    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '(:types  '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += 'interpretation - object )\n'
    res += '(:predicates (true) '
    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            if predicate.split(' ')[0] in contexts.all_predicate_name_in_contexts:
                res += '(' + predicate + ' ?x - interpretation)'
            else:
                res += '(' + predicate + ')'
    res += ')\n'
    for action in problem.actions:
        res += '(:action ' + action.name + '\n'
        res += ':parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'
        if len(action.precondition.parts) != 0 or isinstance(action.precondition, Atom) or isinstance(action.precondition, NegatedAtom):
            res += ':precondition '
            res += '(and \n'
            added_precondition = list()
            for i in range(1, len(sample_list) + 1):
                precondition_command = action.precondition.get_merged_seperated_classical_problem_predicate(contexts, i, added_precondition)
                if precondition_command is not None:
                    res += precondition_command + '\n'
            res += ')'
            res += '\n'
        res += ':effect (and '
        effect_map = dict()
        truth_effect_list = list()
        for effect in action.effects:
            if type(effect.condition) != Truth:
                condition = effect.condition
                if condition in effect_map.keys():
                    effect_map[condition].append(effect.literal)
                else:
                    effect_map[condition] = [effect.literal]
            else:
                truth_effect_list.append(effect.literal)
        for effect in truth_effect_list:
            added_effect = list()
            for i in range(1, len(sample_list) + 1):
                effect_command = effect.get_merged_seperated_classical_problem_predicate(contexts, i, added_effect)
                if effect_command is not None:
                    res += effect_command + '\n'
        if len(effect_map) != 0:
            for condition, effects in effect_map.items():
                for i in range(1, len(sample_list) + 1):
                    res += '(when '
                    res += condition.get_merged_seperated_classical_problem_predicate(contexts, i, [])
                    res += Conjunction(effects).get_merged_seperated_classical_problem_predicate(contexts, i, [])
                    res += ')\n'
        res += '))\n'
    res += ')'
    with open(domain_file, 'w') as f:
        f.write(res)


def writeSeparatedClassicalDomainFile(problem, domain_file, sample_list):
    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '(:types  '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += 'interpretation - object )\n'
    res += '(:predicates (true) '
    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            res += '(' + predicate + ' ?x - interpretation)'
            # for i in range(1, iteration + 1):
            #     res += '(' + predicate + ' int' + str(i) + ' - interpretation)'
    res += ')\n'
    for action in problem.actions:
        res += '(:action ' + action.name + '\n'
        res += ':parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'
        if len(action.precondition.parts) != 0 or isinstance(action.precondition, Atom) or isinstance(
                action.precondition, NegatedAtom):
            res += ':precondition '
            res += '(and \n'
            for i in range(1, len(sample_list) + 1):
                res += action.precondition.get_separated_classical_problem_predicate(i) + '\n'
            res += ')'
            res += '\n'

        res += ':effect (and \n'
        effect_map = dict()
        truth_effect_list = list()
        for effect in action.effects:
            if type(effect.condition) != Truth:
                condition = effect.condition
                if condition in effect_map.keys():
                    effect_map[condition].append(effect.literal)
                else:
                    effect_map[condition] = [effect.literal]
            else:
                truth_effect_list.append(effect.literal)
        for effect in truth_effect_list:
            res += '(and '
            for i in range(1, len(sample_list) + 1):
                res += effect.get_separated_classical_problem_predicate(i)
            res += ')\n'
        if len(effect_map) != 0:
            for condition, effects in effect_map.items():
                for i in range(1, len(sample_list) + 1):
                    res += '(when '
                    res += condition.get_separated_classical_problem_predicate(i)
                    res += Conjunction(effects).get_separated_classical_problem_predicate(i)
                    res += ')\n'
        res += '))\n'
    res += ')'
    with open(domain_file, 'w') as f:
        f.write(res)


def writeClassicalDomainFile(problem, domain_file):
    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '(:types  '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += 'interpretation - object )\n'
    res += '(:predicates (true) '
    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            res += '(' + predicate + ' ?x - interpretation)'
    res += ')\n'
    for action in problem.actions:
        res += '(:action ' + action.name + '\n'
        res += ':parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'
        if len(action.precondition.parts) != 0 or isinstance(action.precondition, Atom) or isinstance(
                action.precondition, NegatedAtom):
            res += ':precondition (forall (?interpr - interpretation)'
            res += action.precondition.get_classical_problem_predicate()
            res += ')\n'
        res += ':effect (and '
        effect_map = dict()
        truth_effect_list = list()
        for effect in action.effects:
            if type(effect.condition) != Truth:
                condition = effect.condition.get_classical_problem_predicate()
                if condition in effect_map.keys():
                    effect_map[condition].append(effect.literal)
                else:
                    effect_map[condition] = [effect.literal]
            else:
                truth_effect_list.append(effect.literal)

        for effect in truth_effect_list:
            res += '(forall (?interpr - interpretation) '
            res += effect.get_classical_problem_predicate()
            res += ')'

        if len(effect_map) != 0:
            for condition, effects in effect_map.items():
                res += '(forall (?interpr - interpretation) '
                res += '(when '
                res += condition
                res += Conjunction(effects).get_classical_problem_predicate()
                res += '))'
        res += '))\n'

    res += ')'
    with open(domain_file, 'w') as f:
        f.write(res)


def write_plan_file(plan, plan_file_path):
    res = ''
    for action in plan:
        res += '(' + action.strip() + ')\n'
    with open(plan_file_path, 'w') as f:
        f.write(res)




def planning(classical_domain_file, classical_instance_file, planner, worker, search_engine=None):
    planner_path = None
    if planner == 'ff':
        planner_path = './pCPCES/classical_planner/ff'
        cmd = [planner_path, '-o', classical_domain_file, '-f', classical_instance_file]
        output = call_planner(cmd, worker)
        plan = extract_ff_plan(output)
        if isinstance(plan, list):
            plan = json.dumps(plan)
            worker.plan = plan
            worker.status = 3
            retry_delay = 0.1
            while True:
                try:
                    worker.save(update_fields=['status', 'plan'], force_update=True)
                    break
                except OperationalError as e:
                    print('planning 3', e, worker.id)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            with open(os.path.join('files', str(worker.task_id), 'has_plan',
                                   str(worker.iteration) + '-' + str(worker.id) + '.txt'), 'w') as g:
                g.write(str(worker.iteration) + '-' + str(worker.id))
            os.remove(os.path.join('files', str(worker.task_id), 'is_planning',
                                   str(worker.iteration) + '-' + str(worker.id) + '.txt'))
            # compute_sample_tags(sub_task_id, problem, plan, action_map, contexts, probabilistic_tag_generator, all_projected_problems,threshold)
        elif plan is None:
            worker.status = 3
            retry_delay = 0.1
            while True:
                try:
                    worker.save(update_fields=['status'], force_update=True)
                    break
                except OperationalError as e:
                    print('planning 5', e, worker.id)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            with open(os.path.join('files', str(worker.task_id), 'planning_finished', str(worker.iteration)+'-'+str(worker.id)+'.txt'), 'w') as f:
                f.write(str(worker.iteration)+'-'+str(worker.id))
            os.remove(os.path.join('files', str(worker.task_id), 'is_planning',
                                   str(worker.iteration) + '-' + str(worker.id) + '.txt'))
        else: # 这里默认其他情况都是被kill的，状态设为1, applied设为False。如何找到被killed还是pddl出错的？
            worker.status = 1
            worker.applied = False
            retry_delay = 0.1
            while True:
                try:
                    worker.save(update_fields=['status', 'applied'], force_update=True)
                    break
                except OperationalError as e:
                    print('planning 7', e, worker.id)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue


    elif planner == 'fd':
        # planner_path = './pCPCES/downward/fast-downward.py'
        # if search_engine == 'LAMA-2011':
        #     cmd = ['python3', planner_path, '--alias', 'seq-sat-lama-2011', classical_domain_file, classical_instance_file]
        # else:
        #     cmd = ['python3', planner_path, classical_domain_file, classical_instance_file, '--search', search_engine]
        # output = call_planner(cmd, worker)
        # plan = extract_fd_plan(output)
        # if plan is not None:
        #     return plan
        # else:
        #     return None

        planner_path = './pCPCES/downward/fast-downward.py'
        if search_engine == 'LAMA-2011':
            cmd = ['python3', planner_path, '--alias', 'seq-sat-lama-2011', classical_domain_file,
                   classical_instance_file]
        else:
            cmd = ['python3', planner_path, classical_domain_file, classical_instance_file, '--search', search_engine]
        output = call_planner(cmd, worker)
        plan = extract_fd_plan(output)
        if isinstance(plan, list):
            plan = json.dumps(plan)
            worker.plan = plan
            worker.status = 3
            retry_delay = 0.1
            while True:
                try:
                    worker.save(update_fields=['status', 'plan'], force_update=True)
                    break
                except OperationalError as e:
                    print('planning 3', e, worker.id)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            with open(os.path.join('files', str(worker.task_id), 'has_plan',
                                   str(worker.iteration) + '-' + str(worker.id) + '.txt'), 'w') as g:
                g.write(str(worker.iteration) + '-' + str(worker.id))
            os.remove(os.path.join('files', str(worker.task_id), 'is_planning',
                                   str(worker.iteration) + '-' + str(worker.id) + '.txt'))
            # compute_sample_tags(sub_task_id, problem, plan, action_map, contexts, probabilistic_tag_generator, all_projected_problems,threshold)
        elif plan is None:
            worker.status = 3
            retry_delay = 0.1
            while True:
                try:
                    worker.save(update_fields=['status'], force_update=True)
                    break
                except OperationalError as e:
                    print('planning 5', e, worker.id)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue
            with open(os.path.join('files', str(worker.task_id), 'planning_finished',
                                   str(worker.iteration) + '-' + str(worker.id) + '.txt'), 'w') as f:
                f.write(str(worker.iteration) + '-' + str(worker.id))
            os.remove(os.path.join('files', str(worker.task_id), 'is_planning',
                                   str(worker.iteration) + '-' + str(worker.id) + '.txt'))
        else:  # 这里默认其他情况都是被kill的，状态设为1, applied设为False。如何找到被killed还是pddl出错的？
            worker.status = 1
            worker.applied = False
            retry_delay = 0.1
            while True:
                try:
                    worker.save(update_fields=['status', 'applied'], force_update=True)
                    break
                except OperationalError as e:
                    print('planning 7', e, worker.id)
                    time.sleep(retry_delay)
                    retry_delay *= 1 + random.random() * 0.5
                    continue


    elif planner == 'mad':
        planner_path = './pCPCES/classical_planner/DisjunctiveMadagascar/main.py'
        cmd = ['python3', planner_path, '-domain', classical_domain_file, '-instance', classical_instance_file, '-C', '1.2', '-S', '1', '-P', '2', '-F', '1', '-T', '50']
        output = call_planner(cmd, worker)
        plan = extract_mad_plan(output)
        if plan is not None:
            return plan
        else:
            return None


def call_planner(cmd, worker):
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    planner_pid = process.pid
    worker.planner_pid = planner_pid
    retry_delay = 0.1
    while True:
        try:
            worker.save(update_fields=['planner_pid'], force_update=True)
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
    if stderr == '' or 'WARNING' in stderr:
        return stdout
    else:
        return None

def write_no_empty_plan_domain_file(problem, classical_domain_file):
    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '(:types  '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += ')\n'
    res += '(:predicates '
    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            res += '( ' + predicate +')\n'
    res += '( no_empty )\n'
    res += ')\n'
    for action in problem.actions:
        res += '(:action ' + action.name + '\n'
        res += ':parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'
        res += ':precondition '
        res += action.precondition.get_superfd_predicate()
        res += '\n'
        res += ':effect (and '
        effect_map = dict()
        truth_effect_list = list()
        for effect in action.effects:
            if type(effect.condition) != Truth:
                condition = effect.condition.get_superfd_predicate()
                if condition in effect_map.keys():
                    effect_map[condition].append(effect.literal)
                else:
                    effect_map[condition] = [effect.literal]
            else:
                truth_effect_list.append(effect.literal)

        for effect in truth_effect_list:
            res += effect.get_superfd_predicate()

        if len(effect_map) != 0:
            for condition, effects in effect_map.items():
                res += '(when '
                res += condition
                res += Conjunction(effects).get_superfd_predicate()
                res += ')'
        res += '))\n'
    res += '''
(:action magic
:parameters  ()
:effect (no_empty))'''
    res += ')'
    with open(classical_domain_file, 'w') as f:
        f.write(res)

def write_no_empty_plan_instance_file(problem, sample_list, start_init, classical_instance_file):
    closed = set()
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        if obj not in problem.constants:
            obj = str(obj).split(': ')
            res += '  ' + obj[0] + ' - ' + obj[1] + '\n'
    res += ')\n'
    res += '(:init\n'
    res += '(and\n'
    for item in start_init:
        predicate = item.predicate
        if not predicate.startswith('='):
            res += item.get_superfd_predicate() + '\n'
            closed.add(item.get_superfd_predicate())
    counter_example_set = sample_list[-1]
    for counter_example in counter_example_set:
        if '(' + counter_example + ') ' not in closed:
            res += '(' + counter_example + ')\n'
    res += '  (not (no_empty))\n'
    res += ')\n'
    res += ')\n'
    res += '(:goal '
    res += problem.goal.get_superfd_predicate()
    res = res[:-2]
    res += ' (no_empty))'
    res += '))'
    with open(classical_instance_file, 'w') as f:
        f.write(res)

def writeSampleFile(sample_list, problem, classical_instance_file, contexts=None, merged=True, separated=True):
    if not merged and not separated:
        writeClassicalSampleFile(sample_list, problem, classical_instance_file)
    elif merged and not separated:
        writeMergedClassicalSampleFile(sample_list, problem, classical_instance_file, contexts)
    elif not merged and separated:
        writeSeparatedClassicalSampleFile(sample_list, problem, classical_instance_file)
    else:
        writeMergedSeparatedClassicalSampleFile(sample_list, problem, classical_instance_file, contexts)

def writeDomainFile(problem, classical_domain_file, sample_list=None, contexts=None, merged=True, separated=True):
    if not merged and not separated:
        writeClassicalDomainFile(problem, classical_domain_file)
    elif merged and not separated:
        writeMergedClassicalDomainFile(problem, classical_domain_file, contexts)
    elif not merged and separated:
        writeSeparatedClassicalDomainFile(problem, classical_domain_file, sample_list)
    else:
        writeMergedSeparatedClassicalDomainFile(problem, classical_domain_file, contexts, sample_list)