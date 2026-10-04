#!/usr/bin/env python3
"""Finite A/B solution-equivalence probe for callback endpoint propagation.

B's completed endpoint check is modeled as a relation over three independently
synthesized coordinates. A safe early step projects the complete B solution
set onto unary endpoint domains, while retaining both B relations and the
final joint query. It must preserve the exact solution set. An endpoint-copy
mutants demonstrate why assigning expected coordinates or erasing method,
adapter, residual, or evidence alternatives is stronger.

This is a finite scheduling characterization, not Yulang Function semantics,
constraint generation, or proof that a production propagator computes only
logical consequences.

Run: python3 tools/research_callback_ab_solution_equivalence.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from random import Random


POINTS = tuple(product((0, 1), repeat=3))
RELATIONS = tuple(
    frozenset(points for bit, points in enumerate(POINTS) if mask & (1 << bit))
    for mask in range(1 << len(POINTS))
)
METHODS = ("method-left", "method-right")
ADAPTERS = ("adapter-left", "adapter-right")


@dataclass(frozen=True, order=True)
class Witness:
    method: str
    adapter: str
    residual: str
    evidence: str


WITNESSES = tuple(
    Witness(method, adapter, f"residual-{i}", f"evidence-{i}")
    for i, (method, adapter) in enumerate(product(METHODS, ADAPTERS))
)


def b_solutions(body_constraints, completed_inequality, witness_map=None):
    """Synthesis, one ordinary query, and their retained evidence choices."""
    endpoints = body_constraints & completed_inequality
    if witness_map is None:
        witness_map = {endpoint: frozenset(WITNESSES) for endpoint in endpoints}
    return frozenset(
        (endpoint, witness)
        for endpoint in endpoints
        for witness in witness_map.get(endpoint, frozenset())
    )


def safe_a_solutions(body_constraints, completed_inequality, witness_map=None):
    """Propagate only coordinate values supported by a complete B solution."""
    complete = b_solutions(body_constraints, completed_inequality, witness_map)
    supported = tuple(
        frozenset(endpoint[coordinate] for endpoint, _witness in complete)
        for coordinate in range(3)
    )
    # A is only a scheduling optimization: retain the full constraints/query.
    return frozenset(
        solution
        for solution in b_solutions(body_constraints, completed_inequality, witness_map)
        for row, _witness in (solution,)
        if all(row[i] in supported[i] for i in range(3))
    )


def copy_expected_endpoint_mutant(body_constraints, completed_inequality, expected):
    """Wrongly equate synthesized endpoints with the expected endpoint."""
    return frozenset(
        solution
        for solution in b_solutions(body_constraints, completed_inequality)
        for row, _witness in (solution,)
        if row == expected
    )


def erase_evidence_mutant(solutions):
    """Wrongly keep only one method/adapter witness per endpoint."""
    selected = {}
    for endpoint, witness in sorted(solutions):
        selected.setdefault(endpoint, (endpoint, witness))
    return frozenset(selected.values())


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


def randomized_tagged_exhaustion():
    """Vary per-endpoint method/evidence alternatives without erasing them."""
    rng = Random(20261005)
    cases = 0
    for _ in range(2048):
        body = rng.choice(RELATIONS)
        inequality = rng.choice(RELATIONS)
        witness_map = {
            endpoint: frozenset(
                witness
                for bit, witness in enumerate(WITNESSES)
                if rng.getrandbits(1)
            )
            for endpoint in POINTS
        }
        expected = b_solutions(body, inequality, witness_map)
        optimized = safe_a_solutions(body, inequality, witness_map)
        assert optimized == expected
        cases += 1
    return cases


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


def minimum_evidence_erasure_counterexample():
    endpoint = POINTS[0]
    body = frozenset({endpoint})
    inequality = frozenset({endpoint})
    witnesses = frozenset(WITNESSES[:2])
    solutions = frozenset((endpoint, witness) for witness in witnesses)
    mutant = erase_evidence_mutant(solutions)
    assert len(solutions) == 2 and len(mutant) == 1
    return endpoint, solutions, mutant


def main() -> None:
    cases, nonempty = exhaust()
    tagged_cases = randomized_tagged_exhaustion()
    body, inequality, expected, original, copied = minimum_copy_counterexample()
    assert len(body) == len(inequality) == 1
    assert len(original) == len(WITNESSES) and not copied
    endpoint, tagged, erased = minimum_evidence_erasure_counterexample()
    print(f"finite B/A relation pairs checked: {cases}")
    print(f"pairs with at least one B solution: {nonempty}")
    print("full-solution projection propagation with final query retained: exact")
    print(
        f"tagged method/adapter/residual/evidence cases checked: {tagged_cases}; "
        "all alternatives preserved"
    )
    print(
        "minimum endpoint-copy failure (retaining all tagged B witnesses): "
        f"body={sorted(body)}, inequality={sorted(inequality)}, "
        f"expected={expected}, B={sorted(original)}, mutant={sorted(copied)}"
    )
    print(
        "minimum evidence-erasure failure: "
        f"endpoint={endpoint}, B has {len(tagged)} choices, mutant has {len(erased)}"
    )
    print(
        "scope: three binary endpoint coordinates and arbitrary finite relations; "
        "no Function ports, production propagator, or Yulang evidence derivation"
    )


if __name__ == "__main__":
    main()
