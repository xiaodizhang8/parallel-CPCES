import sys

from pCPCES.translate.graph import transitive_closure
from pCPCES.translate.pddl.predicates import Predicate
from pCPCES.translate.pddl.functions import Function
from pCPCES.translate.pddl.conditions import Conjunction
from pCPCES.translate.pddl.conditions import Disjunction
from pCPCES.translate.pddl.conditions import UniversalCondition
from pCPCES.translate.pddl.conditions import ExistentialCondition
from pCPCES.translate.pddl.conditions import NegatedAtom
from pCPCES.translate.pddl.conditions import Atom
from pCPCES.translate.pddl.conditions import Literal
from pCPCES.translate.pddl.effects import ConjunctiveEffect
from pCPCES.translate.pddl.conditions import Truth
from pCPCES.translate.pddl.effects import UniversalEffect
from pCPCES.translate.pddl.effects import ConditionalEffect
from pCPCES.translate.pddl.effects import SimpleEffect
from pCPCES.translate.pddl.effects import Effect
from pCPCES.translate.pddl.effects import CostEffect
from pCPCES.translate.pddl.f_expression import NumericConstant
from pCPCES.translate.pddl.f_expression import PrimitiveNumericExpression
from pCPCES.translate.pddl.f_expression import Assign
from pCPCES.translate.pddl.f_expression import Increase
from pCPCES.translate.pddl.actions import Action
from pCPCES.translate.pddl.axioms import Axiom
from pCPCES.translate.pddl.tasks import Requirements
from pCPCES.translate.pddl.tasks import Task
from pCPCES.translate.pddl.pddl_types import Type
from pCPCES.translate.pddl.pddl_types import TypedObject


def parse_typed_list(alist, only_variables=False,
                     constructor=TypedObject,
                     default_type="object"):
    result = []
    while alist:
        try:
            separator_position = alist.index("-")
        except ValueError:
            items = alist
            _type = default_type
            alist = []
        else:
            items = alist[:separator_position]
            _type = alist[separator_position + 1]
            alist = alist[separator_position + 2:]
        for item in items:
            assert not only_variables or item.startswith("?"), \
                   "Expected item to be a variable: %s in (%s)" % (
                item, " ".join(items))
            entry = constructor(item, _type)
            result.append(entry)
    return result


def set_supertypes(type_list):
    # TODO: This is a two-stage construction, which is perhaps
    # not a great idea. Might need more thought in the future.
    type_name_to_type = {}
    child_types = []
    for type in type_list:
        type.supertype_names = []
        type_name_to_type[type.name] = type
        if type.basetype_name:
            child_types.append((type.name, type.basetype_name))
    for (desc_name, anc_name) in transitive_closure(child_types):
        type_name_to_type[desc_name].supertype_names.append(anc_name)


def parse_predicate(alist):
    name = alist[0]
    arguments = parse_typed_list(alist[1:], only_variables=True) # adj [<TypedObject ?i: pos>, <TypedObject ?j: pos>]
    return Predicate(name, arguments)


def parse_function(alist, type_name):
    name = alist[0]
    arguments = parse_typed_list(alist[1:])
    return Function(name, arguments, type_name)


def parse_condition(alist, type_dict, predicate_dict):
    """
    <pddl.conditions.Conjunction object at 0x100bd8ac0>
    Atom located(?i)
    Atom obj_at(?o, ?i)
    """
    condition = parse_condition_aux(alist, False, type_dict, predicate_dict)
    return condition.uniquify_variables({}).simplified()


def parse_condition_aux(alist, negated, type_dict, predicate_dict):
    """Parse a PDDL condition. The condition is translated into NNF on the fly."""
    tag = alist[0]
    if tag in ("and", "or", "not", "imply"):
        args = alist[1:]
        if tag == "imply":
            assert len(args) == 2
        if tag == "not":
            assert len(args) == 1
            return parse_condition_aux(
                args[0], not negated, type_dict, predicate_dict)
    elif tag in ("forall", "exists"):
        parameters = parse_typed_list(alist[1])
        args = alist[2:]
        assert len(args) == 1
    else:
        return parse_literal(alist, type_dict, predicate_dict, negated=negated)

    if tag == "imply":
        parts = [parse_condition_aux(
                args[0], not negated, type_dict, predicate_dict),
                 parse_condition_aux(
                args[1], negated, type_dict, predicate_dict)]
        tag = "or"
    else:
        parts = [parse_condition_aux(part, negated, type_dict, predicate_dict)
                 for part in args]

    if tag == "and" and not negated or tag == "or" and negated:
        return Conjunction(parts)
    elif tag == "or" and not negated or tag == "and" and negated:
        return Disjunction(parts)
    elif tag == "forall" and not negated or tag == "exists" and negated:
        return UniversalCondition(parameters, parts)
    elif tag == "exists" and not negated or tag == "forall" and negated:
        return ExistentialCondition(parameters, parts)


def parse_literal(alist, type_dict, predicate_dict, negated=False):
    if alist[0] == "not":
        assert len(alist) == 2
        alist = alist[1]
        negated = not negated

    pred_id, arity = _get_predicate_id_and_arity(
        alist[0], type_dict, predicate_dict)

    if arity != len(alist) - 1:
        raise SystemExit("predicate used with wrong arity: (%s)"
                         % " ".join(alist))

    if negated:
        return NegatedAtom(pred_id, alist[1:])
    else:
        return Atom(pred_id, alist[1:])


SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH = False
def _get_predicate_id_and_arity(text, type_dict, predicate_dict):
    global SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH

    the_type = type_dict.get(text)
    the_predicate = predicate_dict.get(text)

    if the_type is None and the_predicate is None:
        raise SystemExit("Undeclared predicate: %s" % text)
    elif the_predicate is not None:
        if the_type is not None and not SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH:
            msg = ("Warning: name clash between type and predicate %r.\n"
                   "Interpreting as predicate in conditions.") % text
            print(msg, file=sys.stderr)
            SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH = True
        return the_predicate.name, the_predicate.get_arity()
    else:
        assert the_type is not None
        return the_type.get_predicate_name(), 1


def parse_effects(alist, result, type_dict, predicate_dict):
    """Parse a PDDL effect (any combination of simple, conjunctive, conditional, and universal)."""
    tmp_effect = parse_effect(alist, type_dict, predicate_dict)
    normalized = tmp_effect.normalize()
    cost_eff, rest_effect = normalized.extract_cost()
    add_effect(rest_effect, result)
    if cost_eff:
        return cost_eff.effect
    else:
        return None

def add_effect(tmp_effect, result):
    """tmp_effect has the following structure:
       [ConjunctiveEffect] [UniversalEffect] [ConditionalEffect] SimpleEffect."""

    if isinstance(tmp_effect, ConjunctiveEffect):
        for effect in tmp_effect.effects:
            add_effect(effect, result)
        return
    else:
        parameters = []
        condition = Truth()
        if isinstance(tmp_effect, UniversalEffect):
            parameters = tmp_effect.parameters
            if isinstance(tmp_effect.effect, ConditionalEffect):
                condition = tmp_effect.effect.condition
                assert isinstance(tmp_effect.effect.effect, SimpleEffect)
                effect = tmp_effect.effect.effect.effect
            else:
                assert isinstance(tmp_effect.effect, SimpleEffect)
                effect = tmp_effect.effect.effect
        elif isinstance(tmp_effect, ConditionalEffect):
            condition = tmp_effect.condition
            assert isinstance(tmp_effect.effect, SimpleEffect)
            effect = tmp_effect.effect.effect
        else:
            assert isinstance(tmp_effect, SimpleEffect)
            effect = tmp_effect.effect
        assert isinstance(effect, Literal)
        # Check for contradictory effects
        condition = condition.simplified()
        new_effect = Effect(parameters, condition, effect)
        contradiction = Effect(parameters, condition, effect.negate())
        if contradiction not in result:
            result.append(new_effect)
        else:
            # We use add-after-delete semantics, keep positive effect
            if isinstance(contradiction.literal, NegatedAtom):
                result.remove(contradiction)
                result.append(new_effect)

def parse_effect(alist, type_dict, predicate_dict):
    tag = alist[0]
    if tag == "and":
        return ConjunctiveEffect(
            [parse_effect(eff, type_dict, predicate_dict) for eff in alist[1:]])
    elif tag == "forall":
        assert len(alist) == 3
        parameters = parse_typed_list(alist[1])
        effect = parse_effect(alist[2], type_dict, predicate_dict)
        return UniversalEffect(parameters, effect)
    elif tag == "when":
        assert len(alist) == 3
        condition = parse_condition(
            alist[1], type_dict, predicate_dict)
        effect = parse_effect(alist[2], type_dict, predicate_dict)
        return ConditionalEffect(condition, effect)
    elif tag == "increase":
        assert len(alist) == 3
        assert alist[1] == ['total-cost']
        assignment = parse_assignment(alist)
        return CostEffect(assignment)
    else:
        # We pass in {} instead of type_dict here because types must
        # be static predicates, so cannot be the target of an effect.
        return SimpleEffect(parse_literal(alist, {}, predicate_dict))


def parse_expression(exp):
    if isinstance(exp, list):
        functionsymbol = exp[0]
        return PrimitiveNumericExpression(functionsymbol, exp[1:])
    elif exp.replace(".", "").isdigit():
        return NumericConstant(float(exp))
    elif exp[0] == "-":
        raise ValueError("Negative numbers are not supported")
    else:
        return PrimitiveNumericExpression(exp, [])

def parse_assignment(alist):
    assert len(alist) == 3
    op = alist[0]
    head = parse_expression(alist[1])
    exp = parse_expression(alist[2])
    if op == "=":
        return Assign(head, exp)
    elif op == "increase":
        return Increase(head, exp)
    else:
        assert False, "Assignment operator not supported."


def parse_action(alist, type_dict, predicate_dict):
    iterator = iter(alist)
    action_tag = next(iterator)
    assert action_tag == ":action"
    name = next(iterator)
    parameters_tag_opt = next(iterator)
    if parameters_tag_opt == ":parameters":
        parameters = parse_typed_list(next(iterator),
                                      only_variables=True)
        precondition_tag_opt = next(iterator)
    else:
        parameters = []
        precondition_tag_opt = parameters_tag_opt
    if precondition_tag_opt == ":precondition":
        precondition_list = next(iterator)
        if not precondition_list:
            # Note that :precondition () is allowed in PDDL.
            precondition = Conjunction([])
        else:
            precondition = parse_condition(
                precondition_list, type_dict, predicate_dict)
        effect_tag = next(iterator)
    else:
        precondition = Conjunction([])
        effect_tag = precondition_tag_opt
    assert effect_tag == ":effect"
    effect_list = next(iterator)
    eff = []
    if effect_list:
        try:
            cost = parse_effects(
                effect_list, eff, type_dict, predicate_dict)
        except ValueError as e:
            raise SystemExit("Error in Action %s\nReason: %s." % (name, e))
    for rest in iterator:
        assert False, rest
    if eff:
        return Action(name, parameters, len(parameters),
                           precondition, eff, cost)
    else:
        return None


def parse_axiom(alist, type_dict, predicate_dict):
    assert len(alist) == 3
    assert alist[0] == ":derived"
    predicate = parse_predicate(alist[1])
    condition = parse_condition(
        alist[2], type_dict, predicate_dict)
    return Axiom(predicate.name, predicate.arguments,
                      len(predicate.arguments), condition)


def parse_task(domain_pddl, task_pddl):
    domain_name, domain_requirements, types, type_dict, constants, predicates, predicate_dict, functions, actions, axioms \
                 = parse_domain_pddl(domain_pddl)
    task_name, task_domain_name, task_requirements, objects, init, unknown_inits, disjunction_inits, goal, use_metric = parse_task_pddl(task_pddl, type_dict, predicate_dict)
    assert domain_name == task_domain_name
    requirements = Requirements(sorted(set(
                domain_requirements.requirements +
                task_requirements.requirements)))
    objects = constants + objects
    check_for_duplicates(
        [o.name for o in objects],
        errmsg="error: duplicate object %r",
        finalmsg="please check :constants and :objects definitions")
    init += [Atom("=", (obj.name, obj.name)) for obj in objects]

    return Task(
        domain_name, task_name, requirements, types, objects,
        predicates, functions, init, goal, actions, axioms, use_metric, unknown_inits, disjunction_inits)


def parse_domain_pddl(domain_pddl):
    iterator = iter(domain_pddl)

    define_tag = next(iterator)
    assert define_tag == "define"
    domain_line = next(iterator)
    assert domain_line[0] == "domain" and len(domain_line) == 2
    yield domain_line[1]

    ## We allow an arbitrary order of the requirement, types, constants,
    ## predicates and functions specification. The PDDL BNF is more strict on
    ## this, so we print a warning if it is violated.
    requirements = Requirements([":strips"])
    the_types = [Type("object")]
    constants, the_predicates, the_functions = [], [], []
    correct_order = [":requirements", ":types", ":constants", ":predicates",
                     ":functions"]
    seen_fields = []
    first_action = None
    for opt in iterator:
        field = opt[0]
        if field not in correct_order:
            first_action = opt
            break
        if field in seen_fields:
            raise SystemExit("Error in domain specification\n" +
                             "Reason: two '%s' specifications." % field)
        if (seen_fields and
            correct_order.index(seen_fields[-1]) > correct_order.index(field)):
            msg = "\nWarning: %s specification not allowed here (cf. PDDL BNF)" % field
            print(msg, file=sys.stderr)
        seen_fields.append(field)
        if field == ":requirements":
            requirements = Requirements(opt[1:])
        elif field == ":types":
            the_types.extend(parse_typed_list(
                    opt[1:], constructor=Type))
        elif field == ":constants":
            constants = parse_typed_list(opt[1:])
        elif field == ":predicates":
            the_predicates = [parse_predicate(entry)
                              for entry in opt[1:]]
            the_predicates += [Predicate("=", [
                TypedObject("?x", "object"),
                TypedObject("?y", "object")])]
        elif field == ":functions":
            the_functions = parse_typed_list(
                opt[1:],
                constructor=parse_function,
                default_type="number")
    set_supertypes(the_types)
    yield requirements
    yield the_types
    type_dict = {type.name: type for type in the_types}
    yield type_dict
    yield constants
    yield the_predicates
    predicate_dict = {pred.name: pred for pred in the_predicates}
    yield predicate_dict
    yield the_functions

    entries = []
    if first_action is not None:
        entries.append(first_action)
    entries.extend(iterator)

    the_axioms = []
    the_actions = []
    for entry in entries:
        if entry[0] == ":derived":
            axiom = parse_axiom(entry, type_dict, predicate_dict)
            the_axioms.append(axiom)
        else:
            action = parse_action(entry, type_dict, predicate_dict)
            if action is not None:
                the_actions.append(action)
    yield the_actions
    yield the_axioms

def parse_initial(fact):
    initial_true = list()
    initial_unknown = list()
    initial_true.append(fact[0])
    print(fact)
    for init in fact[1:]:
        if init[0] != 'oneof':
            initial_true.append(init)
        else:
            initial_unknown.append(init[1:])

    # print(initial_true)
    # print(initial_unknown)
    # print('8')
    return initial_true, initial_unknown


def parse_task_pddl(task_pddl, type_dict, predicate_dict):
    iterator = iter(task_pddl)

    define_tag = next(iterator)
    assert define_tag == "define"
    problem_line = next(iterator)
    assert problem_line[0] == "problem" and len(problem_line) == 2
    yield problem_line[1]
    domain_line = next(iterator)
    assert domain_line[0] == ":domain" and len(domain_line) == 2
    yield domain_line[1]

    requirements_opt = next(iterator)
    if requirements_opt[0] == ":requirements":
        requirements = requirements_opt[1:]
        objects_opt = next(iterator)
    else:
        requirements = []
        objects_opt = requirements_opt
    yield Requirements(requirements)

    if objects_opt[0] == ":objects":
        yield parse_typed_list(objects_opt[1:])
        init = next(iterator)
    else:
        yield []
        init = objects_opt

    assert init[0] == ":init"
    initial = []
    initial_true = set()
    initial_false = set()
    initial_unknown = set()
    unknown_init_groups = list()
    disjunction_init_groups = list()
    initial_assignments = dict()
    for fact in init[1:]:
        if fact[0] == "=":
            try:
                assignment = parse_assignment(fact)
            except ValueError as e:
                raise SystemExit("Error in initial state specification\n" +
                                 "Reason: %s." % e)
            if not isinstance(assignment.expression,
                              NumericConstant):
                raise SystemExit("Illegal assignment in initial state " +
                                 "specification:\n%s" % assignment)
            if assignment.fluent in initial_assignments:
                prev = initial_assignments[assignment.fluent]
                if assignment.expression == prev.expression:
                    print("Warning: %s is specified twice" % assignment,
                          "in initial state specification")
                else:
                    raise SystemExit("Error in initial state specification\n" +
                                     "Reason: conflicting assignment for " +
                                     "%s." % assignment.fluent)
            else:
                initial_assignments[assignment.fluent] = assignment
                initial.append(assignment)
        elif fact[0] == "not":
            atom = Atom(fact[1][0], fact[1][1:])
            check_atom_consistency(atom, initial_true, initial_false, initial_unknown, 'false')
            initial_false.add(atom)
        elif fact[0] == 'and':
            for sub_fact in fact[1:]:
                if sub_fact[0] == 'oneof':
                    unknown_group = list()
                    for unknown_fact in sub_fact[1:]:
                        atom = Atom(unknown_fact[0],unknown_fact[1:])
                        check_atom_consistency(atom, initial_true, initial_false, initial_unknown, 'unknown')
                        unknown_group.append(atom)
                    unknown_init_groups.append(unknown_group)
                elif sub_fact[0] == 'or':
                    disjunction_group = list()
                    for disjunct_fact in sub_fact[1:]:
                        if disjunct_fact[0] == 'not':
                            atom = NegatedAtom(disjunct_fact[1][0], disjunct_fact[1][1:])
                        else:
                            atom = Atom(disjunct_fact[0], disjunct_fact[1:])
                        disjunction_group.append(atom)
                    disjunction_init_groups.append(disjunction_group)
                else:
                    atom = Atom(sub_fact[0], sub_fact[1:])
                    # Here may have a bug if initial predicate is negative
                    check_atom_consistency(atom, initial_true, initial_false, initial_unknown, 'true')
                    initial_true.add(atom)
        elif fact[0] == 'unknown':
            atom = Atom(fact[1][0], fact[1][1:])
            check_atom_consistency(atom, initial_true, initial_false, initial_unknown, 'unknown')
            initial_unknown.add(atom)
        else:
            atom = Atom(fact[0], fact[1:])
            check_atom_consistency(atom, initial_true, initial_false, initial_unknown, 'true')
            initial_true.add(atom)
    initial.extend(initial_true)
    yield initial
    yield unknown_init_groups
    yield disjunction_init_groups
    goal = next(iterator)
    assert goal[0] == ":goal" and len(goal) == 2
    yield parse_condition(goal[1], type_dict, predicate_dict)

    use_metric = False
    for entry in iterator:
        if entry[0] == ":metric":
            if entry[1] == "minimize" and entry[2][0] == "total-cost":
                use_metric = True
            else:
                assert False, "Unknown metric."
    yield use_metric

    for entry in iterator:
        assert False, entry


def check_atom_consistency(atom, initial_true, initial_false, initial_unknown, option="true"):
    if option == 'true':
        if atom in initial_false or atom in initial_unknown:
            raise SystemExit("Error in initial state specification\n" +
                             "Reason: %s is (true and false) or (true and unknown)." % atom)
        if atom in initial_true:
            print("Warning: %s is specified twice in initial state specification" % atom)
    elif option == 'false':
        if atom in initial_true or atom in initial_unknown:
            raise SystemExit("Error in initial state specification\n" +
                             "Reason: %s is (true and false) or (false and unknown)." % atom)
        if atom in initial_false:
            print("Warning: %s is specified twice in initial state specification" % atom)
    elif option == 'unknown':
        if atom in initial_true or atom in initial_false:
            raise SystemExit("Error in initial state specification\n" +
                             "Reason: %s is (true and unknown) or (false and unknown)." % atom)
        if atom in initial_unknown:
            print("Warning: %s is specified twice in initial state specification" % atom)


def check_for_duplicates(elements, errmsg, finalmsg):
    seen = set()
    errors = []
    for element in elements:
        if element in seen:
            errors.append(errmsg % element)
        else:
            seen.add(element)
    if errors:
        raise SystemExit("\n".join(errors) + "\n" + finalmsg)
