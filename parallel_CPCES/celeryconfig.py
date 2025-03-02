from __future__ import absolute_import
from celery import Celery
from django.conf import settings
from kombu import Queue, Exchange
import os





CELERY_ACKS_LATE = True
CELERYD_PREFETCH_MULTIPLIER= 1 # 对于预取的，顺序无法变更，所以设置数量为1.注意0代表不限制
CELERYD_CONCURRENCY= 1
CELERY_QUEUES= (
    # Queue("celery", Exchange("celery"), routing_key="celery", priority=101),
    Queue("planning", Exchange("planning"), routing_key="planning", queue_arguments={'x-max-priority': 255}),
    Queue("hitting", Exchange("hitting"), routing_key="hitting")
    # Queue("celery_demo_high", Exchange("celery_demo_high"), routing_key="celery_demo_high", priority=9)
)
CELERY_ROUTES = {
    'tasks.classical_planning': {"queue": "planning", "routing_key": "planning"},
    'tasks.check_hitting_skipping': {"queue": "hitting", "routing_key": "hitting"}
}
BROKER_TRANSPORT_OPTIONS = {
    'priority_steps': list(range(250)), # 设置优先级最多容忍多少，默认是4个（0，3，6，9），参考https://stackoverflow.com/questions/15239880/task-priority-in-celery-with-redis
    'queue_order_strategy': 'priority',
}

# BROKER_URL = 'redis://127.0.0.1:6379'  # 指定 Broker
# CELERY_RESULT_BACKEND = 'redis://127.0.0.1:6379/0'  # 指定 Backend
BROKER_URL = 'pyamqp://'
CELERY_RESULT_BACKEND = 'rpc://'

CELERY_IMPORTS = (  # 指定导入的任务模块
    'parallel_CPCES.tasks',
)

# 设置系统的环境配置用的是Django的
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "parallel_CPCES.settings")
# 实例化celery
app = Celery('luna_eval', broker=BROKER_URL, backend=CELERY_RESULT_BACKEND)

# APP设置时区
app.conf.timezone = 'Australia/ACT'

app.autodiscover_tasks(lambda : settings.INSTALLED_APPS)

app.conf.broker_transport_options = {
    'queue_order_strategy': 'priority',
}