# import options

from pCPCES.translate.pddl_parser.lisp_parser import parse_nested_list
from pCPCES.translate.pddl_parser.lisp_parser import ParseError
from pCPCES.translate.pddl_parser.parsing_functions import parse_task
from pCPCES.translate.pddl_parser.parsing_functions import parse_probabilistic_task

file_open = open


def parse_pddl_file(type, filename):
    try:
        # The builtin open function is shadowed by this module's open function.
        # We use the Latin-1 encoding (which allows a superset of ASCII, of the
        # Latin-* encodings and of UTF-8) to allow special characters in
        # comments. In all other parts, we later validate that only ASCII is
        # used.
        return parse_nested_list(file_open(filename,
                                                       encoding='ISO-8859-1'))
    except OSError as e:
        raise SystemExit("Error: Could not read file: %s\nReason: %s." %
                         (e.filename, e))
    except ParseError as e:
        raise SystemExit("Error: Could not parse %s file: %s\nReason: %s." %
                         (type, filename, e))


def open_pddl(domain_filename=None, task_filename=None, type='conformant_planning'): # type可以是conformant_planning或者conformant_probabilistic_planning
    task_filename = task_filename or options.task
    domain_filename = domain_filename or options.domain

    domain_pddl = parse_pddl_file("domain", domain_filename)
    task_pddl = parse_pddl_file("task", task_filename)
    if type == 'conformant_planning':
        return parse_task(domain_pddl, task_pddl)
    elif type == 'conformant_probabilistic_planning':
        return parse_probabilistic_task(domain_pddl, task_pddl)
