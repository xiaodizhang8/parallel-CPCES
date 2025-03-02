import os
import subprocess
import argparse
from translate.pddl_parser.pddl_file import open as open_problem
from translate.pddl.conditions import Atom, NegatedAtom, Truth
from translate.pddl.conditions import UniversalCondition, Disjunction, Conjunction
import time


def parse(domain, instance):
    problem = open_problem(domain, instance)
    return problem


def write_new_domain(problem, domain):
    goal = problem.goal
    single_goal_index = 0
    sub_goal_index = 0
    additional_actions = ''
    if isinstance(goal, UniversalCondition):
        real_goal = goal.parts[0]
        if isinstance(real_goal, Disjunction):
            partial_goals = real_goal.parts
            for partial_goal in partial_goals:
                additional_actions += '    (:action achieve-partial-goal' + str(single_goal_index) + '\n'
                additional_actions += '        :precondition '
                additional_actions += '(forall (' + goal.parameters[0].name + ' - ' + goal.parameters[
                    0].type_name + ') '
                additional_actions += partial_goal.pddl_dump()
                additional_actions += ')\n'
                additional_actions += '        :effect (achieved' + str(sub_goal_index) + ')\n'
                additional_actions += '    )\n'
                single_goal_index += 1
            sub_goal_index += 1
        elif isinstance(real_goal, Conjunction):
            sub_goals = real_goal.parts
            for sub_goal in sub_goals:
                partial_goals = sub_goal.parts
                for partial_goal in partial_goals:
                    additional_actions += '    (:action achieve-partial-goal' + str(single_goal_index) + '\n'
                    additional_actions += '        :precondition '
                    additional_actions += '(forall (' + goal.parameters[0].name + ' - ' + goal.parameters[
                        0].type_name + ') '
                    additional_actions += partial_goal.pddl_dump()
                    additional_actions += ')\n'
                    additional_actions += '        :effect (achieved' + str(sub_goal_index) + ')\n'
                    additional_actions += '    )\n'
                sub_goal_index += 1
    else:
        if isinstance(goal, Disjunction):
            partial_goals = goal.parts
            for partial_goal in partial_goals:
                additional_actions += '    (:action achieve-partial-goal' + str(single_goal_index) + '\n'
                additional_actions += '        :precondition '
                additional_actions += partial_goal.pddl_dump()
                additional_actions += '\n'
                additional_actions += '        :effect (achieved' + str(sub_goal_index) + ')\n'
                additional_actions += '    )\n'
                single_goal_index += 1
            sub_goal_index += 1
        elif isinstance(goal, Conjunction):
            sub_goals = goal.parts
            for sub_goal in sub_goals:
                partial_goals = sub_goal.parts
                for partial_goal in partial_goals:
                    additional_actions += '    (:action achieve-partial-goal' + str(single_goal_index) + '\n'
                    additional_actions += '        :precondition '
                    additional_actions += partial_goal.pddl_dump()
                    additional_actions += '\n'
                    additional_actions += '        :effect (achieved' + str(sub_goal_index) + ')\n'
                    additional_actions += '    )\n'
                    single_goal_index += 1
                sub_goal_index += 1

    additional_actions += '    (:action achieve-goal\n'
    if isinstance(goal, UniversalCondition):
        goal = goal.parts[0]
    if isinstance(goal, Disjunction):
        additional_actions += '        :precondition (achieved0)\n'
        additional_actions += '        :effect (achieved)\n'
        additional_actions += '    )\n'
    elif isinstance(goal, Conjunction):
        index = 0
        additional_actions += '        :precondition (and '
        sub_goals = goal.parts
        for sub_goal in sub_goals:
            additional_actions += '(achieved' + str(index) + ') '
            index += 1
        additional_actions += ')\n'
        additional_actions += '        :effect (achieved)\n'
        additional_actions += '    )\n'


    res = '(define (domain ' + problem.domain_name + ')\n'
    res += '    (:types '
    for predicate_type in problem.types:
        res += predicate_type.name + ' - '
        if predicate_type.basetype_name is None:
            res += 'null '
        else:
            res += predicate_type.basetype_name + ' '
    res += ')\n'

    res += '    (:predicates '
    for predicate in problem.predicates:
        if not str(predicate).startswith('='):
            predicate = str(predicate).replace('(', ' ').replace(':', ' -').replace(',', '').replace(')', '')
            res += '(' + predicate + ')'
    for i in range(sub_goal_index):
        res += ' (achieved' + str(i) + ')'
    res += ' (achieved)'
    res += ')\n'

    for action in problem.actions:
        res += '    (:action ' + action.name + '\n'
        res += '        :parameters ('
        for parameter in action.parameters:
            parameter = str(parameter).replace(':', ' -')
            res += parameter + ' '
        res += ')\n'

        precondition = action.precondition
        res += '        :precondition (and \n'
        res += '        (not (and '
        for i in range(sub_goal_index):
            res += '(achieved' + str(i) + ') '
        res += '))\n'
        if isinstance(precondition, Atom) or isinstance(precondition, NegatedAtom):
            res += '        (' + precondition.predicate + ' ' + ' '.join(precondition.args) + '))\n'
        elif len(precondition.parts) != 0:
            if isinstance(precondition, UniversalCondition):
                res += '         (forall (' + precondition.parameters[0].name + ' - ' + \
                       precondition.parameters[0].type_name + ') '
                predicates = precondition.parts[0]
                res += predicates.pddl_dump()
                res += '))\n'
            else:
                res += '         '
                res += precondition.pddl_dump()
                res += ')\n'
        else:
            res += '        )\n'
        res += '        :effect (and \n'
        effects = action.effects

        for effect in effects:
            has_forall = False
            has_condition = False
            if effect.parameters:
                res += '        (forall (' + effect.parameters[0].name + ' - ' + effect.parameters[0].type_name + ') '
                has_forall = True
            if not isinstance(effect.condition, Truth):
                if isinstance(effect.condition, Disjunction):
                    res += '(when (and (not (and '
                    for predicate in effect.condition.parts:
                        predicate = predicate.negate()
                        res += predicate.pddl_dump()
                    res += ')))'
                else:
                    res += '(when ' + effect.condition.pddl_dump()
                has_condition = True
            res_literal = effect.literal.pddl_dump()
            if not has_condition and not has_forall:
                res += '        ' + res_literal
            else:
                res += res_literal
            if has_forall:
                res += ')'
            if has_condition:
                res += ')'
            res += '\n'
        res += '        )\n'
        res += '    )\n'

    res += additional_actions
    res += ')'

    with open(domain, 'w') as f:
        f.write(res)


def write_new_instance(problem, instance):
    res = '(define (problem ' + problem.task_name + ')(:domain ' + problem.domain_name + ')(:objects\n'
    for obj in problem.objects:
        obj = str(obj).split(': ')
        res += ' ' + obj[0] + ' - ' + obj[1] + '\n'
    res += ')\n'
    res += '(:init\n'
    # print(problem.init)
    for predicate in problem.init:
        if predicate.predicate != '=':
            res += ' ' + predicate.pddl_dump() + '\n'
    res += ')\n'
    res += '(:goal (achieved))\n'
    res += ')'
    with open(instance, 'w') as f:
        f.write(res)


def check_disjunctive_goal(problem):
    goal = problem.goal
    if isinstance(goal, Atom) or isinstance(goal, NegatedAtom):
        return False
    if isinstance(goal, UniversalCondition):
        goal = goal.parts[0]
    if isinstance(goal, Disjunction):
        return True

    q = list()
    q.append(goal)
    while len(q) != 0:
        node = q.pop(0)
        if isinstance(node, Disjunction):
            return True
        if len(node.parts) != 0:
            for child in node.parts:
                q.append(child)
    return False


def planning(domain, instance, A=None, B=None, C=None, M=None, S=None, F=None, T=None, P=None, one=None, O=None, X=None,
             Q=None, o=None, b=None, t=None, r=None, m=None, N=None, c=None, W=None, i=None, R=None):
    command = ['./classical_planner/DisjunctiveMadagascar/M', domain, instance]
    if A is not None:
        command.append('-A')
        command.append(str(A))
    if A is not None:
        command.append('-B')
        command.append(str(B))
    if C is not None:
        command.append('-C')
        command.append(str(C))
    if M is not None:
        command.append('-M')
        command.append(str(M))
    if S is not None:
        command.append('-S')
        command.append(str(S))
    if F is not None:
        command.append('-F')
        command.append(str(F))
    if T is not None:
        command.append('-T')
        command.append(str(T))
    if P is not None:
        command.append('-P')
        command.append(str(P))
    if one is not None:
        command.append('-1')
        command.append(str(one))
    if O is not None:
        command.append('-O')
        command.append(str(O))
    if X is not None:
        command.append('-X')
        command.append(str(X))
    if Q is not None:
        command.append('-Q')
        command.append(str(Q))
    if o is not None:
        command.append('-o')
        command.append(str(o))
    if b is not None:
        command.append('-b')
        command.append(str(b))
    if t is not None:
        command.append('-t')
        command.append(str(t))
    if r is not None:
        command.append('-r')
        command.append(str(r))
    if m is not None:
        command.append('-m')
        command.append(str(m))
    if N is not None:
        command.append('-N')
        command.append(str(N))
    if c is not None:
        command.append('-c')
        command.append(str(c))
    if W is not None:
        command.append('-W')
        command.append(str(W))
    if i is not None:
        command.append('-i')
        command.append(str(i))
    if R is not None:
        command.append('-R')
        command.append(str(R))
    p = subprocess.Popen(command, stdout=subprocess.PIPE)
    for line in iter(p.stdout.readline, b''):
        print(line)
    p.stdout.close()
    p.wait()


def run(domain, instance, A=None, B=None, C=None, M=None, S=None, F=None, T=None, P=None, one=None, O=None, X=None,
        Q=None, o=None, b=None, t=None, r=None, m=None, N=None, c=None, W=None, i=None, R=None):
    problem = parse(domain, instance)
    has_disjunctions = check_disjunctive_goal(problem)
    if has_disjunctions:
        current_time = time.time()
        domain = domain + str(current_time) + 'new'
        instance = instance + str(current_time) + 'new'
        write_new_domain(problem, domain)
        write_new_instance(problem, instance)
    planning(domain, instance, A=A, B=B, C=C, M=M, S=S, F=F, T=T, P=P, one=one, O=O, X=X, Q=Q, o=o, b=b, t=t, r=r, m=m,
             N=N, c=c, W=W, i=i, R=R)
    if has_disjunctions:
        os.remove(domain)
        os.remove(instance)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-domain', dest='domain')
    parser.add_argument('-instance', dest='instance')
    parser.add_argument('-A', dest='A', help='Run algorithm A with parameter n (range 1 to 50)')
    parser.add_argument('-B', dest='B', help='Run algorithm B with parameter r (range 0.1 to 0.9999) default -B 0.90.')
    parser.add_argument('-C', dest='C', help='Run algorithm C with parameter r (range 1.2 to 2.0)')
    parser.add_argument('-M', dest='M', help='With algorithm B, use maximum n processes (default -M 20).')
    parser.add_argument('-S', dest='S',
                        help='Step for horizon lengths 0,n,2n,3n,... (default -S 5, algorithms A and B only)')
    parser.add_argument('-F', dest='F', help='Starting horizon length (default -F 0)')
    parser.add_argument('-T', dest='T', help='Ending horizon length (default -T 3000)')
    parser.add_argument('-P', dest='P', help='''
    Choose plan type n:  (default -P 2)
           0 = sequential plans
           1 = A-step plans (Graphplan parallelism)
           2 = E-step plans (Rintanen et al. 2004, 2006)''')
    parser.add_argument('-1', dest='one', help='Force at least one action every step')
    parser.add_argument('-O', dest='O', help='Write formulas in a file in DIMACS format instead of solving.')
    parser.add_argument('-X', dest='X', help='Don\'t use PDDL semantics for simultaneous v:=0 v:=1.')
    parser.add_argument('-Q', dest='Q', help='Output plans in the IPC format.')
    parser.add_argument('-o', dest='o', help='[filename]  Output plan to file.')
    parser.add_argument('-b', dest='b', help='[filename]  Name for the DIMACS CNF files.')
    parser.add_argument('-t', dest='t', help='Timeout n seconds of CPU time')
    parser.add_argument('-r', dest='r', help='Timeout n seconds of real time')
    parser.add_argument('-m', dest='m', help='Allocating max. n MB of memory (default -m 12288)')
    parser.add_argument('-N', dest='N', help='Don\'t compute invariants.')
    parser.add_argument('-c', dest='c', help='Don\'t eliminate converse literals.')
    parser.add_argument('-W', dest='W', help='Use time as the random seed (instead of seed 0).')
    parser.add_argument('-i', dest='i', help='Restart interval is n (default -i 60).')
    parser.add_argument('-R', dest='R', help='Restart scheme n=0 constant n=1 Luby (default -R 0).')
    args = parser.parse_args()
    run(args.domain, args.instance, args.A, args.B, args.C, args.M, args.S, args.F, args.T, args.P, args.one, args.O,
        args.X, args.Q, args.o, args.b, args.t, args.r, args.m, args.N, args.c, args.W, args.i, args.R)
