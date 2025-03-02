


def extract_ff_plan(output):
    plan = list()
    if 'ff: found legal plan as follows' in output:
        output = str(output).split('\n')
        found_plan_line = False
        for line in output:
            line = line.strip()
            if line.startswith('step'):
                found_plan_line = True
            if found_plan_line and line == '':
                break
            if found_plan_line and 'REACH-GOAL' not in line:
                line = line.split(':')
                if len(line) > 1:
                    action = line[1].strip()
                    plan.append(action)
        return plan
    elif 'problem proven unsolvable' in output:
        return None
    elif 'simplified to FALSE' in output:
        return None
    else:
        return 'unknown'

def extract_fd_plan(output):
    plan = list()
    if 'Solution found!' in output:
        output = str(output).split('\n')
        # 寻找solution found的行数
        index = 0
        for line in output:
            line = line.strip()
            if 'Solution found!' in line:
                break
            index += 1
        # 读取plan
        for index in range(index+2, len(output)):
            line = output[index].strip()
            if 'Plan length' in line:
                break
            action = ' '.join(line.split()[:-1]).upper()
            plan.append(action)
        return plan
    else:
        return None

def extract_mad_plan(output):
    plan = list()
    found_plan_line = False
    output = str(output).split('\n')
    for line in output:
        line = line[2:-3]
        line = line.strip(': ')
        if found_plan_line and not line.startswith('STEP'):
            break
        if line.startswith('PLAN FOUND:'):
            line = line.split()
            if line[1] == '0 steps':
                return None
            found_plan_line = True
            continue
        if found_plan_line and line.startswith('STEP'):
            line = line.split(': ')[1]
            actions = line.split(' ')
            for action in actions:
                action = action.replace('(', ' ').replace(',', ' ').replace(')', '')
                action = action.upper()
                action = action.strip()
                if action.startswith('ACHIEVE-PARTIAL-GOAL'):
                    continue
                if action == 'ACHIEVE-GOAL':
                    return plan
                plan.append(action)
    if found_plan_line:
        return plan
    else:
        return None
