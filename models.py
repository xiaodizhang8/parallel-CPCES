from django.db import models
from pCPCES.confs import PLANNING_TASK_STATUS
from pCPCES.confs import TASK_STATUS

# Create your models here.
class Task(models.Model):
    domain_name = models.CharField(verbose_name='Domain Name', max_length=200)
    instance_name = models.CharField(verbose_name='Instance Name', max_length=200)
    probability_threshold = models.FloatField(verbose_name='Probability Threshold')
    status = models.IntegerField(choices=TASK_STATUS, verbose_name='Task Status')
    plan = models.TextField(verbose_name='Plan', null=True)
    searching_time = models.FloatField(verbose_name='Searching Time', null=True)
    domain_path = models.TextField(verbose_name='Domain Path')
    instance_path = models.TextField(verbose_name='Instance Path')
    num_workers = models.IntegerField(verbose_name='num_workers', default=0)
    sample_tags_history = models.TextField(verbose_name='Sample Tags History', default='[]')
    update_time =models.DateTimeField(auto_now=True)



class WorkerTask(models.Model):
    task = models.ForeignKey(Task, on_delete=models.PROTECT)
    iteration = models.IntegerField(verbose_name='Iteration')
    classical_domain_name = models.CharField(verbose_name='Classical Domain Name', max_length=200)
    classical_instance_name = models.CharField(verbose_name='Classical Instance Name', max_length=200)
    weight = models.FloatField(verbose_name='Weight')
    status = models.IntegerField(choices=PLANNING_TASK_STATUS, verbose_name='Task Status')
    tag_task_started = models.BooleanField(choices=TASK_STATUS, verbose_name='tag_task_started', default=False)
    hitting_set_index = models.TextField(verbose_name='Hitting Set Index')
    plan = models.TextField(verbose_name='Plan', null=True)
    has_sample_tags = models.BooleanField(verbose_name='has_sample_tags', null=True)
    sample_tag_index = models.TextField(verbose_name='sample_tag_index', null=True)
    tags_probability = models.FloatField(verbose_name='Probability of Tags', default=0, null=True)
    used_projected_problems = models.TextField(verbose_name='used_projected_problems', null=True)
    searching_time = models.FloatField(verbose_name='Searching Time', null=True)
    classical_domain_path = models.TextField(verbose_name='Classical Domain Path')
    classical_instance_path = models.TextField(verbose_name='Classical Instance Path')
    reused_iteration = models.IntegerField(verbose_name='Reused Iteration', null=True)
    pid = models.IntegerField(verbose_name='pid', null=True)
    planner_pid = models.IntegerField(verbose_name='planner_pid', null=True)
    pool_index = models.IntegerField(verbose_name='pool index', null=True)
    planner = models.TextField(verbose_name='Planner')
    search_engine = models.TextField(verbose_name='Search Engine', null=True)
    update_time = models.DateTimeField(auto_now=True)
    applied = models.BooleanField(verbose_name='applied', default=False)
    first_priority = models.FloatField(verbose_name='first_priority', default=1) # 只有1 和 0， 0为第一优先级，只有在算tag的时候用

class HittingTask(models.Model):
    task = models.ForeignKey(Task, on_delete=models.PROTECT)
    iteration = models.IntegerField(verbose_name='Iteration')
    status = models.IntegerField(choices=TASK_STATUS, verbose_name='Task Status')
    existed_task_ids = models.TextField(verbose_name='existed_subtask_ids', default='[]')
    used_hitting_sets = models.TextField(verbose_name='used_hitting_sets')
    update_time = models.DateTimeField(auto_now=True)
    pid = models.IntegerField(verbose_name='pid', null=True)
    hitter_pid = models.IntegerField(verbose_name='hitter_pid', null=True)
    this_round_hitting_sets_num = models.IntegerField(verbose_name='this_round_hitting_sets_num', default=0)
    pool_index = models.IntegerField(verbose_name='pool index', null=True)
    applied = models.BooleanField(verbose_name='applied', default=False)
    sample_tags_history = models.TextField(verbose_name='Sample Tags History', default='[]')
    used_projected_problems = models.TextField(verbose_name='used_projected_problems', null=True)

class TagTask(models.Model):
    task = models.ForeignKey(Task, on_delete=models.PROTECT)
    planning_task = models.ForeignKey(WorkerTask, on_delete=models.PROTECT)
    sample_tags_index = models.TextField(verbose_name='Sample Tags Index', null=True)
    sample_tags_index_by_group = models.TextField(verbose_name='Sample Tags Index by Group', null=True)
    status = models.IntegerField(choices=TASK_STATUS, verbose_name='Task Status')
    update_time = models.DateTimeField(auto_now=True)
    pid = models.IntegerField(verbose_name='pid', null=True)

