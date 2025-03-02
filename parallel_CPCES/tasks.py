from __future__ import absolute_import, unicode_literals
from parallel_CPCES import app
# from pCPCES.Methods.classical_planning import planning
# from pCPCES.ConformantProbabilisticPlanning.HittingSet import check_skipping
import time

# @app.task
# def classical_planning(classical_domain_path, classical_instance_path, planner, sub_task_id, search_engine):
#     return planning(classical_domain_path, classical_instance_path, planner, sub_task_id, search_engine)
#
# @app.task
# def check_hitting_skipping(planning_task_id, hitting_task_id, sample_tags_history, all_true_and_false_tags_by_index, iteration, num_workers):
#     check_skipping(planning_task_id, hitting_task_id, sample_tags_history, all_true_and_false_tags_by_index, iteration, num_workers)
#     return

@app.task
def mul(x, y):
    time.sleep(1)
    print(x*y)
    return x * y

@app.task
def xsum(numbers):
    time.sleep(1)
    print(sum(numbers))
    return sum(numbers)