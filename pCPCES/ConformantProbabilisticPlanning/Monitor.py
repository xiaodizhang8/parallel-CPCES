import time
from pCPCES.models import WorkerTask
from pCPCES.models import HittingTask
from django.db.models import Q
import random
import multiprocessing
import os
import signal
from django.db import OperationalError
import glob


def find_files(directory, file_pattern):
    search_path = os.path.join(directory, file_pattern)
    matching_files = glob.glob(search_path)
    return matching_files

def check_has_plan(current_iteration, planning_task):
    has_plan_files = os.listdir(os.path.join('files', str(planning_task.id), 'has_plan'))
    for file in has_plan_files:
        if file.startswith(str(current_iteration)):
            worker_id = file.split('-')[1].split('.')[0]
            return worker_id
    return None

def round_monitor(current_iteration, planning_task):
    worker_id = check_has_plan(current_iteration, planning_task)
    if worker_id is not None:
        retry_delay = 0.1
        while True:
            try:
                worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id=worker_id))
                if len(worker_tasks) != 0:
                    worker_task = worker_tasks[0]
                    break
            except OperationalError as e:
                print('round_monitor 1', e)
                time.sleep(retry_delay)
                retry_delay *= 1 + random.random() * 0.5
                continue
        return worker_task

    else:
        # case1: hitting task finished
        if os.path.exists(os.path.join('files', str(planning_task.id), 'hitting_finished', str(current_iteration) + '.txt')):
            # case 1.1 planning tasks finished
            waiting_workers = find_files(os.path.join('files', str(planning_task.id), 'planning'), str(current_iteration) + '-*.txt')
            doing_workers = find_files(os.path.join('files', str(planning_task.id), 'is_planning'), str(current_iteration) + '-*.txt')
            if len(waiting_workers) == 0 and len(doing_workers) == 0:
                worker_id = check_has_plan(current_iteration, planning_task)
                if worker_id is not None:# cases 1.1.1 has a plan
                    retry_delay = 0.1
                    while True:
                        try:
                            worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id=worker_id))
                            if len(worker_tasks) != 0:
                                worker_task = worker_tasks[0]
                                break
                        except OperationalError as e:
                            print('round_monitor 1', e)
                            time.sleep(retry_delay)
                            retry_delay *= 1 + random.random() * 0.5
                            continue
                    return worker_task
                else:
                    return "No candidate plan"
            else:  # case 1.2 planning tasks not finish
                worker_id = check_has_plan(current_iteration, planning_task)
                if worker_id is not None:  # case 1.2.1 has a plan
                    retry_delay = 0.1
                    while True:
                        try:
                            worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id=worker_id))
                            if len(worker_tasks) != 0:
                                worker_task = worker_tasks[0]
                                break
                        except OperationalError as e:
                            print('round_monitor 1', e)
                            time.sleep(retry_delay)
                            retry_delay *= 1 + random.random() * 0.5
                            continue
                    return worker_task
                else: # case 1.2.2 no plan yet
                    return "Continue searching"
        else:  # case 2 hitting task not finish
            worker_id = check_has_plan(current_iteration, planning_task)
            if worker_id is not None:  # case 2.1 has a plan
                retry_delay = 0.1
                while True:
                    try:
                        worker_tasks = WorkerTask.objects.select_for_update(nowait=True).filter(Q(id=worker_id))
                        if len(worker_tasks) != 0:
                            worker_task = worker_tasks[0]
                            break
                    except OperationalError as e:
                        print('round_monitor 1', e)
                        time.sleep(retry_delay)
                        retry_delay *= 1 + random.random() * 0.5
                        continue
                return worker_task
            else:
                return "Continue searching"



def kill_planning_task(priority_queue):
    priority_queue.clear()
    working_processes = multiprocessing.active_children()
    for process in working_processes:
        pid = process.pid
        print("killing", pid)
        os.kill(pid, signal.SIGKILL)

def get_status(subprocess=None):
    if subprocess._closed:
        return 'closed'
    if subprocess._popen is None:
        if not subprocess.is_alive():
            return 'initial'
    else:
        exitcode = subprocess._popen.poll()
        if exitcode is not None:
            exitcode = multiprocessing.process._exitcode_to_name.get(exitcode, exitcode)
            return 'stopped'
        else:
            if subprocess._parent_pid != os.getpid():
                return 'unknown'
            else:
                return 'started'

