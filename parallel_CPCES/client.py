# -*- coding: utf-8 -*-
import sys
sys.path.append("..")
from parallel_CPCES import tasks


tasks.mul.delay(2,3)

print('hello world')