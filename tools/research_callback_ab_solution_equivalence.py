#!/usr/bin/env python3
"""Finite A/B solution-equivalence probe for callback endpoint propagation.

B's completed endpoint check is modeled as a relation over three independently
synthesized coordinates. A safe early step projects the complete B solution
set onto unary endpoint domains, while retaining both B relations and the
final joint query. It must preserve the exact solution set. An endpoint-copy
mutant demonstrates why assigning expected coordinates is stronger.

This is a finite scheduling characterization, not Yulang Function semantics,
constraint generation, or proof that a production propagator computes only
logical consequences.

Run: python3 tools/research_callback_ab_solution_equivalence.py
"""

from __future__ import annotations

from itertools import product


POINTS = tuple(product((0, 1), repeat=3))
RELATIONS = tuple(
    frozenset(points for bit, points in enumerate(POINTS) if mask & (1 << bit))
    for mask in range(1 << len(POINTS))
)


def b_solutions(body_constraints: frozenset[tuple[int, ...]], completed_inequality: frozenset[tuple[int, ...]]):
    """Synthesis constraints plus one ordinary completed-interface query."""
    return body_constraints & completed_inequality


def safe_a_solutions(body_constraints, completed_inequality):
    """Propagate only coordinate values supported by a complete B solution."""
    complete = b_solutions(body_constraints, completed_inequality)
    supported = tuple(
        frozenset(row[coordinate] for row in complete)
        for coordinate in range(3)
    )
    # A is only a scheduling optimization: retain the full constraints/query.
    return frozenset(
        row
        for row in b_solutions(body_constraints, completed_inequality)
        if all(row[i] in supported[i] for i in range(3))
    )


def copy_expected_endpoint_mutant(body_constraints, completed_inequality, expected):
    """Wrongly equate synthesized endpoints with the expected endpoint."""
    return frozenset(
        row
        for row in b_solutions(body_constraints, completed_inequality)
        if row == expected
    )


def exhaust():
    cases = 0
    nonempty = 0
    for body, inequality in product(RELATIONS, repeat=2):
        expected = b_solutions(body, inequality)
        optimized = safe_a_solutions(body, inequality)
        assert optimized == expected
        nonempty += bool(expected)
        cases += 1
    assert cases == 256 * 256
    return cases, nonempty


def minimum_copy_counterexample():
    # Minimize relation cardinality first, then the ordered tuple.
    for body_size in range(1, 2):
        for body in RELATIONS:
            if len(body) != body_size:
                continue
            for inequality in RELATIONS:
                if len(inequality) != 1:
                    continue
                for expected in POINTS:
                    original = b_solutions(body, inequality)
                    copied = copy_expected_endpoint_mutant(body, inequality, expected)
                    if original and copied != original:
                        return body, inequality, expected, original, copied
    raise AssertionError("expected endpoint-copy counterexample not found")


def main() -> None:
    cases, nonempty = exhaust()
    body, inequality, expected, original, copied = minimum_copy_counterexample()
    assert len(body) == len(inequality) == 1
    assert len(original) == 1 and not copied
    print(f"finite B/A relation pairs checked: {cases}")
    print(f"pairs with at least one B solution: {nonempty}")
    print("full-solution projection propagation with final query retained: exact")
    print(
        "minimum endpoint-copy failure: "
        f"body={sorted(body)}, inequality={sorted(inequality)}, "
        f"expected={expected}, B={sorted(original)}, mutant={sorted(copied)}"
    )
    print(
        "scope: three binary endpoint coordinates and arbitrary finite relations; "
        "no Function ports, production propagator, or endpoint evidence"
    )


if __name__ == "__main__":
    main()
