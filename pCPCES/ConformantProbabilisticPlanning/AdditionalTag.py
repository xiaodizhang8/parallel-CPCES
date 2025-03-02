import subprocess
import os


def write_cnf(candidate_tag_index, blocked_sets, cnf_path):
    index = 1
    num_clauses = 0
    tag_index_map = dict()
    index_tag_map = dict()

    clauses = ''
    for tag in candidate_tag_index:
        if tag not in tag_index_map.keys():
            index_tag_map[index] = tag
            tag_index_map[tag] = index
            clauses += str(index) + ' '
            index += 1
        else:
            num = tag_index_map[tag]
            clauses += str(num) + ' '
    clauses += '0\n'
    num_clauses += 1

    for blocked in blocked_sets:
        for tag in blocked:
            if tag not in tag_index_map.keys():
                index_tag_map[index] = tag
                tag_index_map[tag] = index
                clauses += '-' + str(index) + ' '
                index += 1
            else:
                num = tag_index_map[tag]
                clauses += '-' + str(num) + ' '
        clauses += '0\n'
        num_clauses += 1

    cnf = f'p cnf {index - 1} {num_clauses}\n'
    cnf += clauses
    with open(cnf_path, 'w') as f:
        f.write(cnf)
    return index_tag_map

def solve_sat_problem(cnf_file):
    kissat_path = './pCPCES/kissat-master/build/kissat'
    # kissat_path = './../kissat-master/build/kissat'
    cmd = [kissat_path, cnf_file]
    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    stdout = process.stdout.read()
    stderr = process.stderr.read().strip()
    if stderr != '':
        print(stderr)
    return stdout

def extract_additional_tags(output, index_tag_map):
    additional_tags = set()
    output = str(output).split('\n')
    for line in output:
        if line.startswith('s'):
            if 'UNSATISFIABLE' in line:
                return None
        if line.startswith('v'):
            line = line.split(' ')[1:]
            for index in line:
                index = int(index)
                if index > 0:
                    tag = index_tag_map[index]
                    additional_tags.add(tag)
    if len(additional_tags) != 0:
        return additional_tags
    else:
        return None

def get_additional_tags(iteration, candidate_tag_index, blocked_sets):
    cnf_path = os.path.join('cnf_temp', 'test-' + str(iteration) + '.cnf')
    index_tag_map = write_cnf(candidate_tag_index, blocked_sets, cnf_path)
    output = solve_sat_problem(cnf_path)
    additional_tags = extract_additional_tags(output, index_tag_map)
    return additional_tags

# if __name__ == '__main__':
#     iteration = 1
#     candidate_tag_index = {0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63}
#     blocked_sets = [[5]]
#     cnf_path = os.path.join('cnf_temp', 'test-' + str(iteration) + '.cnf')
#     index_tag_map = write_cnf(candidate_tag_index, blocked_sets, cnf_path)
#     output = solve_sat_problem(cnf_path)
#     additional_tags = extract_additional_tags(output, index_tag_map)
#     print(additional_tags)