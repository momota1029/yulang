#!/usr/bin/env python3
"""Finite audit of endpoint-dependent dispatch for one inequality judgment.

The model uses only the user-approved optional-record witness from
`2026-10-03-concrete-compatibility-boundary.md`. Variable-to-variable
inequalities form a transitive graph. Any inequality with a concrete endpoint
is retained as an oriented payload or resolved locally; concrete successes
never become graph edges.

The script intentionally does not specify lower/upper replay eligibility,
general record compatibility, casts/adapters, or a complete solver.

Run: python3 tools/research_inequality_endpoint_dispatch.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True, order=True)
class Record:
    optional_foo: str | None


EMPTY = Record(None)
OPT_STRING = Record("string")
OPT_INT = Record("int")
CONCRETE = (EMPTY, OPT_STRING, OPT_INT)
VARIABLES = ("X", "Y", "Z")


@dataclass(frozen=True)
class Inequality:
    left: Record | str
    right: Record | str


def resolve_concrete(left: Record, right: Record) -> bool:
    """The bounded compatibility table, not a general record relation."""
    if left == right:
        return True
    if left == OPT_STRING and right == EMPTY:
        return True
    if left == EMPTY and right == OPT_INT:
        return True
    return False


def dispatch(q: Inequality) -> tuple[str, object]:
    left_var = isinstance(q.left, str)
    right_var = isinstance(q.right, str)
    if left_var and right_var:
        return "variable-edge", (q.left, q.right)
    if not left_var and right_var:
        return "lower-payload", (q.left, q.right)
    if left_var and not right_var:
        return "upper-payload", (q.left, q.right)
    return "local-concrete", (q.left, q.right)


def collect(queries: tuple[Inequality, ...]):
    """Store each endpoint form in its own lane of the one-query solver."""
    edges = set()
    lowers = []
    uppers = []
    local = []
    for query in queries:
        kind, payload = dispatch(query)
        if kind == "variable-edge":
            edges.add(payload)
        elif kind == "lower-payload":
            lowers.append(payload)
        elif kind == "upper-payload":
            uppers.append(payload)
        else:
            left, right = payload
            local.append((payload, resolve_concrete(left, right)))
    return frozenset(edges), tuple(lowers), tuple(uppers), tuple(local)


def transitive_closure(edges: frozenset[tuple[str, str]]) -> frozenset[tuple[str, str]]:
    closure = set(edges)
    changed = True
    while changed:
        changed = False
        for left, middle in tuple(closure):
            for middle2, right in tuple(closure):
                if middle == middle2 and (left, right) not in closure:
                    closure.add((left, right))
                    changed = True
    return frozenset(closure)


def path_oracle(edges: frozenset[tuple[str, str]]) -> frozenset[tuple[str, str]]:
    """Independent adjacency search; reachability requires a nonempty path."""
    adjacency = {node: set() for node in VARIABLES}
    for left, right in edges:
        adjacency[left].add(right)
    reached = set()
    for start in VARIABLES:
        pending = list(adjacency[start])
        seen = set()
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            seen.add(node)
            reached.add((start, node))
            pending.extend(adjacency[node] - seen)
    return frozenset(reached)


def variable_edge_families():
    possible = tuple(product(VARIABLES, repeat=2))
    # Include self edges: the carrier must preserve the harmless reflexive case.
    for mask in range(1 << len(possible)):
        yield frozenset(edge for i, edge in enumerate(possible) if mask & (1 << i))


def dispatch_matrix() -> int:
    cases = 0
    expected = {
        (False, False): "local-concrete",
        (False, True): "lower-payload",
        (True, False): "upper-payload",
        (True, True): "variable-edge",
    }
    for left_var, right_var in product((False, True), repeat=2):
        left = "X" if left_var else EMPTY
        right = "Y" if right_var else EMPTY
        assert dispatch(Inequality(left, right))[0] == expected[(left_var, right_var)]
        cases += 1
    return cases


def variable_graph_exhaustion() -> tuple[int, int]:
    families = 0
    pair_checks = 0
    for edges in variable_edge_families():
        closure = transitive_closure(edges)
        assert closure == path_oracle(edges)
        for x, y, z in product(VARIABLES, repeat=3):
            if (x, y) in edges and (y, z) in edges:
                assert (x, z) in closure
            pair_checks += 1
        # Independently checked closure contains variable nodes only.
        assert all(a in VARIABLES and b in VARIABLES for a, b in closure)
        families += 1
    assert families == 1 << 9
    return families, pair_checks


def concrete_witness() -> tuple[int, int]:
    successes = frozenset(
        (left, right)
        for left, right in product(CONCRETE, repeat=2)
        if resolve_concrete(left, right)
    )
    # Both adjacent concrete inequalities hold, while their proposed composite
    # is a failed local query. This is the approved optional-record witness.
    assert (OPT_STRING, EMPTY) in successes
    assert (EMPTY, OPT_INT) in successes
    assert (OPT_STRING, OPT_INT) not in successes

    # Embedding those comparisons around variable endpoints does not turn the
    # concrete evidence into a variable edge. A witness assignment exists, but
    # the direct endpoint query still resolves locally and fails.
    constraints = (
        Inequality(OPT_STRING, "X"),
        Inequality("X", "Y"),
        Inequality("Y", OPT_INT),
    )
    assert tuple(dispatch(q)[0] for q in constraints) == (
        "lower-payload", "variable-edge", "upper-payload"
    )
    assignment = {"X": EMPTY, "Y": EMPTY}
    assert resolve_concrete(OPT_STRING, assignment["X"])
    assert assignment["X"] == assignment["Y"]
    assert resolve_concrete(assignment["Y"], OPT_INT)
    assert not resolve_concrete(OPT_STRING, OPT_INT)
    return len(successes), len(constraints)


def concrete_successes_are_not_edges() -> int:
    # Exhaust every subset of successful concrete queries through the actual
    # endpoint dispatcher and collector. Local evidence must remain in its own
    # lane and leave variable-edge reachability unchanged.
    successes = tuple(
        Inequality(left, right)
        for left, right in product(CONCRETE, repeat=2)
        if resolve_concrete(left, right)
    )
    checked = 0
    for mask in range(1 << len(successes)):
        selected = tuple(q for i, q in enumerate(successes) if mask & (1 << i))
        edges, lowers, uppers, local = collect(selected)
        closure = transitive_closure(edges)
        assert not closure
        assert not lowers and not uppers
        assert len(local) == len(selected)
        assert all(ok for _, ok in local)
        assert all(dispatch(q)[0] == "local-concrete" for q in selected)
        checked += 1
    return checked


def main() -> None:
    matrix = dispatch_matrix()
    graph_families, graph_checks = variable_graph_exhaustion()
    concrete_success_count, chain_length = concrete_witness()
    subsets = concrete_successes_are_not_edges()
    print(f"endpoint dispatch cases: {matrix}/4")
    print(f"variable-edge graphs: {graph_families}; oracle comparisons: {graph_families}; composition checks: {graph_checks}")
    print(f"successful concrete cells in bounded table: {concrete_success_count}")
    print(f"nontransitive optional-record chain: {chain_length} constraints; direct query fails")
    print(f"subsets of local concrete evidence kept outside edge closure: {subsets}")
    print("scope: endpoint dispatch and approved optional-record witness only; no replay policy or complete solver")


if __name__ == "__main__":
    main()
