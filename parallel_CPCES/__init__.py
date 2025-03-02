# -*- coding: utf-8 -*-

from celery import Celery
# import pymysql
#
# pymysql.install_as_MySQLdb()

app = Celery('parallel_CPCES')  # 创建 Celery 实例
app.config_from_object('parallel_CPCES.celeryconfig')  # 通过 Celery 实例加载配置模块