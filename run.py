# -*- coding: utf-8 -*-
import sys
import time

sys.path.append("..")

import os
os.environ.setdefault("DJANGO_SETTINGS_MODULE", "parallel_CPCES.settings")
import django
django.setup()


from pCPCES.conformant_probability_planning import run


import argparse


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--planning', dest='planning')
    parser.add_argument('-ht', '--hitting', dest='hitting')
    parser.add_argument('-t', '--tag', dest='tag')
    parser.add_argument('-d', '--domain', dest='domain')
    parser.add_argument('-i', '--instance', dest='instance')
    parser.add_argument('-m', '--method', dest='method')
    parser.add_argument('-pl', '--planner', dest='planner')
    args = parser.parse_args()
    print(args.planning)
    print(args.tag)
    run(args.domain, args.instance,int(args.planning), int(args.hitting), int(args.tag), args.method, args.planner)

