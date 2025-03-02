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

# def check_kill(sub_task_id):
#     worker_task = WorkerTask.objects.get(id=sub_task_id)
#     if worker_task.status == 3:
#         # 没有杀成功，因为程序已经结束了
#         print('没有kill成功，晚了一步...')
#         return False
#     elif worker_task.status == 2:
#         # 杀成功了，把状态调整为4
#         print('kill成功')
#         worker_task.status = 4
#         worker_task.save()
#         return True
#
# def check_revoke(sub_task_id):
#     worker_task = WorkerTask.objects.get(id=sub_task_id)
#     if worker_task.status == 2 or worker_task.status == 3:
#         # 没有杀成功，因为程序已经结束了
#         print('没有revoke成功，晚了一步...')
#         return False
#     elif worker_task.status == 1:
#         # 杀成功了，把状态调整为4
#         print('revoke成功')
#         worker_task.status = 4
#         worker_task.save()
#         return True

def find_files(directory, file_pattern):
    # 构建搜索路径
    search_path = os.path.join(directory, file_pattern)
    # 使用 glob 查找匹配的文件
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
    # 这里随机选一个结束的worker的plan作为Candidate plan
    # TODO: 选什么plan最好呢
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
        # 检查本轮hitting结束了
        # case1: hitting 结束的情况下
        if os.path.exists(os.path.join('files', str(planning_task.id), 'hitting_finished', str(current_iteration) + '.txt')):
            # case 1.1 worker 也结束的情况下
            waiting_workers = find_files(os.path.join('files', str(planning_task.id), 'planning'), str(current_iteration) + '-*.txt')
            doing_workers = find_files(os.path.join('files', str(planning_task.id), 'is_planning'), str(current_iteration) + '-*.txt')
            if len(waiting_workers) == 0 and len(doing_workers) == 0:
                worker_id = check_has_plan(current_iteration, planning_task)
                if worker_id is not None:# cases 1.1.1 出现了plan
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
            else:  # case 1.2 worker 还没结束
                worker_id = check_has_plan(current_iteration, planning_task)
                if worker_id is not None:  # case 1.2.1 出现了plan
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
                else: # case 1.2.2 没有plan
                    return "Continue searching"
        else:  # case 2 hitting 还没结束
            worker_id = check_has_plan(current_iteration, planning_task)
            if worker_id is not None:  # case 2.1 出现了plan
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


# def single_plan_monitor(current_iteration, planning_task_id):
#     result = monitor_tasks_in_one_round(current_iteration, planning_task_id)
#     if isinstance(result, str):
#         return None
#     else:
#         return result

# def modifying_task(current_iteration, planning_task_id, planner, search_engine):
#     if current_iteration != 1:
#         worker_tasks = WorkerTask.objects.filter(Q(task_id=planning_task_id) & Q(iteration=current_iteration) & Q(status=2))
#         if len(worker_tasks) == 0:
#             previous_worker_tasks = WorkerTask.objects.filter(Q(task_id=planning_task_id) & Q(iteration__lt=current_iteration) & Q(status=2)).order_by('weight')
#             if len(previous_worker_tasks) != 0:
#                 selected_worker_task = previous_worker_tasks.first()
#                 new_priority = selected_worker_task.weight
#                 new_sub_task_id = kill_and_restart_worker(selected_worker_task, new_priority, planner, search_engine, current_iteration, 'kill')



    # for subtask_id in existed_subtask_id:
    #     print('-')
    #     worker_tasks = WorkerTask.objects.filter(Q(id=subtask_id) & (Q(status=1) | Q(status=2)))
    #     if len(worker_tasks) != 0:
    #         return False
    # return True




# def kill_worker(worker_task):
#     sub_task_id = worker_task.id
#     sig_id = worker_task.sig_id
#     print('尝试杀死: %s' % sig_id)
#     app.control.revoke(task_id=str(sig_id), terminate=True, signal='SIGKILL')
#     stop_succeed = False
#     stop_succeed = check_kill(sub_task_id)
#
# def kill_and_restart_worker(worker_task, new_priority, planner, search_engine, current_iteration, stop_type):
#     sub_task_id = worker_task.id
#     sig_id = worker_task.sig_id
#     print('尝试杀死: %s' % sig_id)
#     app.control.revoke(task_id=str(sig_id), terminate=True, signal='SIGKILL')
#     stop_succeed = False
#     if stop_type == 'kill':
#         stop_succeed = check_kill(sub_task_id)
#     elif stop_type == 'revoke':
#         stop_succeed = check_revoke(sub_task_id)
#     else:
#         print('stop type is wrong...')
#         exit()
#     if stop_succeed:
#         planning_task = worker_task.task
#         iteration = worker_task.iteration
#         domain_name = worker_task.classical_domain_name
#         instance_name = worker_task.classical_instance_name
#         index_hitting_set = worker_task.hitting_set_index
#         classical_domain_path = worker_task.classical_domain_path
#         classical_instance_path = worker_task.classical_instance_path
#         new_sig_id = uuid()
#         sub_task = WorkerTask(task=planning_task, iteration=iteration, classical_domain_name=domain_name,
#                               classical_instance_name=instance_name, weight=new_priority, status=1,
#                               hitting_set_index=index_hitting_set,
#                               classical_domain_path=classical_domain_path,
#                               classical_instance_path=classical_instance_path, reused_iteration=current_iteration,
#                               sig_id=new_sig_id)
#         try:
#             sub_task.save()
#         except:
#             log.exception("save error for WorkerTask")
#             exit()
#         print('重启: %s' % new_sig_id)
#         new_sub_task_id = sub_task.id
#         sig = classical_planning.s(classical_domain_path, classical_instance_path, planner, new_sub_task_id,
#                                    search_engine)
#         sig.apply_async(queue='hitting', priority=new_priority, task_id=new_sig_id)
#         return new_sub_task_id

# def changing_tasks_priority(planning_task_id, existed_subtask_id, current_iteration, planner, search_engine):
#     new_existed_subtask_id = existed_subtask_id
#     # 检查还处于waiting状态的task
#     worker_tasks = WorkerTask.objects.filter(Q(id__in=existed_subtask_id) & Q(status=1))
#     if len(worker_tasks) != 0:
#         # 将waiting状态的task提高priority
#         for worker_task in worker_tasks:
#             new_priority = current_iteration
#             new_sub_task_id = kill_and_restart_worker(worker_task, new_priority, planner, search_engine, current_iteration, 'revoke')
#             new_existed_subtask_id.remove(worker_task.id)
#             new_existed_subtask_id.append(new_sub_task_id)
#     # 检查是否有task已经进入到搜索状态
#     worker_tasks = WorkerTask.objects.filter(Q(id__in=existed_subtask_id) & Q(status=2))
#     if len(worker_tasks) == 0:
#         # 若没有任何一个进入到搜索状态，需要把之前的一个正在运行的task kill掉。我们选择优先级最低的
#         previous_worker_tasks = WorkerTask.objects.filter(
#             Q(task_id=planning_task_id) & Q(iteration__lt=current_iteration) & Q(status=2)).order_by('weight') # order by是由小到大排列
#         if len(previous_worker_tasks) != 0:
#             selected_worker_task = previous_worker_tasks.first()
#             new_priority = selected_worker_task.weight
#             new_sub_task_id = kill_and_restart_worker(selected_worker_task, new_priority, planner, search_engine, current_iteration, 'kill')
#     return new_existed_subtask_id

# def kill_all_not_finished_tasks(task):
#     task_id = task.id
#     worker_tasks = WorkerTask.objects.filter(Q(task_id=task_id) & Q(status=1))
#     for worker_task in worker_tasks:
#         sig_id = worker_task.sig_id
#         print('尝试杀死: %s' % sig_id)
#         result = AsyncResult(sig_id)
#         result.revoke()
#         app.control.revoke(task_id=str(sig_id), terminate=True, signal='SIGKILL')
#         worker_task.status = 4
#         worker_task.save(update_fields=['status'])
#     worker_tasks = WorkerTask.objects.filter(Q(task_id=task_id) & Q(status=2))
#     for worker_task in worker_tasks:
#         sig_id = worker_task.sig_id
#         print('尝试杀死: %s' % sig_id)
#         app.control.revoke(task_id=str(sig_id), terminate=True, signal='SIGKILL')
#         worker_task.status = 4
#         worker_task.save(update_fields=['status'])



# def hitting_monitor(hitting_task_id):
#     previous_hitting_set = None
#     while True:
#         hitting_task = HittingTask.objects.get(id=hitting_task_id)
#         status = hitting_task.status
#         this_round_hitting_sets = hitting_task.this_round_hitting_sets
#         if status == 3:
#             existed_task_ids = hitting_task.existed_task_ids
#             return eval(existed_task_ids), json.loads(this_round_hitting_sets), status
#         if this_round_hitting_sets != previous_hitting_set:
#             existed_task_ids = hitting_task.existed_task_ids
#             return eval(existed_task_ids), json.loads(this_round_hitting_sets), status
#         previous_hitting_set = this_round_hitting_sets

# def modify_priority(this_round_hitting_sets, planning_task_id, priority_deducting_value, planner, search_engine):
#     if this_round_hitting_sets[0][1] - priority_deducting_value > 230:
#         print('减扣优先级')
#         canceled_tasks = WorkerTask.objects.filter(Q(task_id=planning_task_id) & Q(status=1) & Q(weight__lt=130)) # 五轮之前的全部不要了
#         for task in canceled_tasks:
#             kill_all_not_finished_tasks(task)
#         print('不要的task处理结束', planning_task_id)
#         priority_changed_tasks = WorkerTask.objects.filter(Q(task_id=planning_task_id) & Q(status=1) & Q(weight__gte=130)) # 五轮以内的都留着
#         for task in priority_changed_tasks:
#             new_priority = task.weight - 130
#             print(new_priority)
#             kill_and_restart_worker(task, new_priority, planner, search_engine, None, 'revoke')
#         return priority_deducting_value + 130
#     else:
#         return priority_deducting_value


# def kill_hitting_task(hitting_task_id, hitting_processing):
#     hitting_status = get_status(hitting_processing)
#     pid = hitting_processing.pid
#     if hitting_status == 'started':
#         os.kill(pid, signal.SIGKILL)
#         hitting_task = HittingTask.objects.get(id=hitting_task_id)
#         hitting_task.status = 4
#         hitting_task.save(update_fields=['status'])


def kill_planning_task(priority_queue):
    priority_queue.clear()
    working_processes = multiprocessing.active_children()
    for process in working_processes:
        pid = process.pid
        print("正在杀", pid)
        os.kill(pid, signal.SIGKILL)

def get_status(subprocess=None):
    '''
    dict = {
        'initlal': {
            subprocess._popen: None,
            subprocess.is_alive(): False,
        },
        'started': {
            subprocess._popen: is not None,
            subprocess.is_alive(): True,
           subprocess._popen.poll: is not None
        },
        'stopped': {
            subprocess._popen: is not None,
            subprocess.is_alive(): False,
            subprocess._popen.poll: 0                       # if exit as expected
        },
        'closed': {
            subprocess._closed: True
        }
    }
    '''

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

