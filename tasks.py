from __future__ import absolute_import, unicode_literals
from parallel_CPCES import app
import time


@app.task
def mul(x, y):
    time.sleep(10)
    print(x*y)
    return x * y

@app.task
def xsum(numbers):
    time.sleep(10)
    print(sum(numbers))
    return sum(numbers)