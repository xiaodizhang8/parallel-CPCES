# from pCPCES.ConformantProbabilisticPlanning.ClassicalPlanningWriter import write_classical_instance_file_by_hitting_set
# from pCPCES.ConformantProbabilisticPlanning.ClassicalPlanningWriter import write_classical_domain_file_by_hitting_set
# import os
# from pCPCES.models import WorkerTask
# from pCPCES.Methods.classical_planning import planning
#
#
# def start_planning(problem, classical_domain_path, classical_instance_path, merged_problems, probabilistic_tag_generator, index_hitting_set, all_projected_problems, contexts, iteration, planning_task, domain_name, instance_name, priority, planner, search_engine):
#     write_classical_instance_file_by_hitting_set(problem, classical_instance_path, merged_problems,
#                                                  probabilistic_tag_generator, index_hitting_set, all_projected_problems,
#                                                  contexts)
#     write_classical_domain_file_by_hitting_set(problem, classical_domain_path, contexts, index_hitting_set,
#                                                probabilistic_tag_generator, all_projected_problems)
#     pid = os.getpid()
#     sub_task = WorkerTask(task=planning_task, iteration=iteration, classical_domain_name=domain_name,
#                           classical_instance_name=instance_name, weight=priority, status=1,
#                           hitting_set_index=index_hitting_set,
#                           classical_domain_path=os.path.join('pCPCES', classical_domain_path[7:]),
#                           classical_instance_path=os.path.join('pCPCES', classical_instance_path[7:]),
#                           planner=planner, pid=pid, search_engine=search_engine)
#     sub_task.save()
#     sub_task_id = sub_task.id
#     planning(os.path.join('pCPCES', classical_domain_path[7:]),
#                                os.path.join('pCPCES', classical_instance_path[7:]), planner, sub_task_id, search_engine)

# def restart_planning(iteration, id):
#     task = WorkerTask.objects.get(id=int(id))
#     pid = os.getpid()
#     sub_task = WorkerTask(task=task.task, iteration=int(iteration), classical_domain_name=task.classical_domain_name,
#                           classical_instance_name=task.classical_instance_name, weight=task.weight, status=1,
#                           hitting_set_index=task.hitting_set_index,
#                           classical_domain_path=task.classical_domain_path,
#                           classical_instance_path=task.classical_instance_path,
#                           planner=task.planner, pid=pid, search_engine=task.search_engine)
#     sub_task.save()
#     sub_task_id = sub_task.id
#     planning(task.classical_domain_path, task.classical_instance_path, task.planner, sub_task_id, task.search_engine)