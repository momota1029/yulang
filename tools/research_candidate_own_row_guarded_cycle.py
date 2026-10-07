#!/usr/bin/env python3
"""Conditional raw-expansion attack; does not implement Q/R selection or Yulang."""
import itertools
import json
import resource
import signal
import time


def deadline(_signal, _frame):
    raise TimeoutError("10-second hard stop; enumeration incomplete")


signal.signal(signal.SIGALRM, deadline)
signal.alarm(10)
START = time.monotonic()
FULL = 7


def function(argument, result):
    # Universe: i (bit 0), constant-i callable k (bit 1), identity h (bit 2).
    # Concrete total tables: k(x)=i; h(x)=x, for every universe token x.
    return ((2 if argument == 0 or result & 1 else 0)
            | (4 if argument & ~result == 0 else 0))


FUNCTION = tuple(tuple(function(a, b) for b in range(8)) for a in range(8))


def expand(graph, row, polarity, active=(), guard_depth=0, alias=False):
    edges, side, argument, result, scalar = graph
    state = (row, polarity)
    prior_depth = next((depth for key, depth in active if key == state), None)
    if prior_depth is not None:
        # The mutation aliases only an active owner's identity, not its own leaf.
        return ("v", (row + 1) % 3 if alias else row), {(row, guard_depth > prior_depth)}
    active += ((state, guard_depth),)
    parts = [("v", row)]
    reentries = set()
    targets = [a for a, b in edges if b == row] if polarity == 1 else [
        b for a, b in edges if a == row]
    for target in targets:
        value, traces = expand(graph, target, polarity, active, guard_depth, alias)
        parts.append(value)
        reentries |= traces
    if row == 0 and polarity == side:
        av, at = expand(graph, argument, -polarity, active, guard_depth + 1, alias)
        rv, rt = expand(graph, result, polarity, active, guard_depth + 1, alias)
        parts.append(("f", av, rv))
        reentries |= at | rt
    if row == 2 and polarity == scalar:
        parts.append(("c", 1))
    return (("u" if polarity == 1 else "n", tuple(parts)), reentries)


def compile_forest(expressions):
    nodes, ids = [], {}

    def intern(expression):
        if expression in ids:
            return ids[expression]
        kind = expression[0]
        if kind in ("v", "c"):
            node = expression
        elif kind == "f":
            node = (kind, intern(expression[1]), intern(expression[2]))
        else:
            node = (kind, tuple(intern(child) for child in expression[1]))
        index = len(nodes)
        nodes.append(node)
        ids[expression] = index
        return index

    roots = [intern(expression) for expression in expressions]
    return nodes, roots


def evaluate(forest, assignment):
    nodes, roots = forest
    values = []
    for node in nodes:
        kind = node[0]
        if kind == "v":
            value = assignment[node[1]]
        elif kind == "c":
            value = node[1]
        elif kind == "f":
            value = FUNCTION[values[node[1]]][values[node[2]]]
        else:
            value = 0 if kind == "u" else FULL
            for child in node[1]:
                if kind == "u":
                    value |= values[child]
                else:
                    value &= values[child]
        values.append(value)
    return [values[root] for root in roots]


def satisfies(graph, assignment):
    edges, side, argument, result, scalar = graph
    if any(assignment[a] & ~assignment[b] for a, b in edges):
        return False
    bound = FUNCTION[assignment[argument]][assignment[result]]
    if (bound & ~assignment[0] if side == 1 else assignment[0] & ~bound):
        return False
    return not (1 & ~assignment[2] if scalar == 1 else
                assignment[2] & ~1 if scalar == -1 else 0)


def main():
    possible_edges = tuple((a, b) for a in range(3) for b in range(3) if a != b)
    edge_sets = [()] + [(edge,) for edge in possible_edges] + list(
        itertools.combinations(possible_edges, 2))
    assignments = tuple(itertools.product(range(8), repeat=3))
    count = satisfying = cyclic = guarded = 0
    mutation_witness = direct_mutation_witness = None
    for edges, side, argument, result, scalar in itertools.product(
            edge_sets, (1, -1), range(3), range(3), (0, 1, -1)):
        graph = (edges, side, argument, result, scalar)
        count += 1
        assert count <= 5000
        expressions, traces = [], set()
        for row, polarity in itertools.product(range(3), (1, -1)):
            expression, seen = expand(graph, row, polarity)
            expressions.append(expression)
            traces |= seen
        cyclic += bool(traces)
        guarded += any(is_guarded for _, is_guarded in traces)
        forest = compile_forest(expressions)
        mutant = None if mutation_witness and direct_mutation_witness else compile_forest([
            expand(graph, row, polarity, alias=True)[0]
            for row, polarity in itertools.product(range(3), (1, -1))])
        for assignment in assignments:
            if not satisfies(graph, assignment):
                continue
            satisfying += 1
            expected = [value for value in assignment for _ in (1, -1)]
            observed = evaluate(forest, assignment)
            if observed != expected:
                raise AssertionError(("candidate failure", graph, assignment,
                                      expected, observed))
            if mutant:
                mutated = evaluate(mutant, assignment)
                if mutated != expected:
                    witness = dict(graph=graph, assignment=assignment,
                                   expected=expected, observed=mutated)
                    if mutation_witness is None:
                        mutation_witness = witness
                    if edges and direct_mutation_witness is None:
                        direct_mutation_witness = witness
    # One-row repeated-port witness: split h's argument/result coordinates.
    # Shared q=Bottom permits k,h; independently replace argument by Top, retain
    # result Bottom, and both are lost. This is a mutation, not the candidate.
    assert FUNCTION[0][0] == 6 and FUNCTION[7][0] == 0
    assert mutation_witness is not None and direct_mutation_witness is not None
    print(json.dumps(dict(
        claim="conditional finite raw-expansion characterization",
        graphs=count, assignments_per_graph=len(assignments),
        assignment_candidates=count * len(assignments),
        satisfying_assignments=satisfying, row_side_equalities=6 * satisfying,
        cyclic_graphs=cyclic, guarded_reentry_graphs=guarded,
        active_owner_alias_mutation=mutation_witness,
        direct_active_owner_alias_mutation=direct_mutation_witness,
        repeated_port_split=dict(shared_q=0, independent_argument=7,
                                 retained_result=0, before=6, after=0),
        seed=None, elapsed_seconds=round(time.monotonic() - START, 6),
        max_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss),
        sort_keys=True))


if __name__ == "__main__":
    main()
