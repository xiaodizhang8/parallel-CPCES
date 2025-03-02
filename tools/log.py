import logging
import os
from parallel_CPCES.settings import CPCES_LOG_LEVEL

# Django项目普通日志
log = logging.getLogger("parallel_CPCES")

# Celery任务日志,通过调用setup_logger对于不同的task, 不同的product,生成自己的日志文件
# 注意: logger_file请给出绝对路径!
def setup_logger(log_file):
    log_path = os.path.split(log_file)[0]
    logger_name = log_file.replace('/', '_')
    try:
        if not os.path.isdir(log_path):
            os.makedirs(log_path)
    except FileExistsError:
        pass
    l = logging.getLogger(logger_name)
    formatter = logging.Formatter('%(asctime)s-%(name)s-%(filename)s-%(funcName)s:%(lineno)s:%(levelname)s: %(message)s')
    fileHandler = logging.FileHandler(log_file, mode='a')
    fileHandler.setFormatter(formatter)
    l.setLevel(CPCES_LOG_LEVEL)
    l.addHandler(fileHandler)
    return logger_name
