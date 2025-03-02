from pCPCES.models import WorkerTask
from django.db.models import Q


# def check_existed_hitting_set(hitting_set, planning_task_id, current_iteration):
#     '''
#     如果这轮hitting set里面有曾经完成过的task，那就直接跳过本轮
#     '''
#     subtask_id_set = set()
#     worker_tasks = WorkerTask.objects.filter(Q(task_id=planning_task_id) & Q(iteration__lt=current_iteration) & Q(hitting_set_index=str(hitting_set)) & (Q(status=1)|Q(status=2)|Q(status=3))).values('id')
#     if len(worker_tasks) != 0:
#         for worker in worker_tasks:
#             sub_task_id = worker['id']
#             subtask_id_set.add(sub_task_id)
#     return subtask_id_set



