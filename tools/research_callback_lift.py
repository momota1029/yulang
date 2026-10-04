#!/usr/bin/env python3
"""Finite stress model for Theorem C's old-tuple-preserving callback lift.

This is a proof-search model, not a callback semantics or source compiler. It
checks the local §2.6 invariant: derived output coordinates are total
functions of one source witness, while old tuple fields and d-/d+/b+
occurrence identities remain attached to that witness. It also searches for
the smallest failure caused by replacing the joint relation with independent
marginals.

Run: python3 tools/research_callback_lift.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations


@dataclass(frozen=True, order=True)
class Witness:
    # One fixed nu,K,D fiber and one original source tuple.
    fiber: tuple[int, int, int]
    arg_origin: int
    body_origin: int
    result: int
    # Existing evidence identities; the lift must not freshen or conflate them.
    d_minus: str = "d-"
    d_plus: str = "d+"
    b_plus: str = "b+"

    def observe(self) -> tuple[object, ...]:
        return (
            self.fiber,
            self.arg_origin,
            self.body_origin,
            self.result,
            self.d_minus,
            self.d_plus,
            self.b_plus,
        )


@dataclass(frozen=True, order=True)
class Lifted:
    old: Witness
    # Total derived logical coordinates: both are computed on the same tuple.
    d_projection: tuple[int, ...]
    b_projection: tuple[int, ...]
    flat_output: tuple[int, ...]


def total_lift(w: Witness) -> Lifted:
    d = (w.arg_origin,)
    b = (w.body_origin, w.result)
    return Lifted(w, d, b, tuple(sorted(set(d) | set(b))))


def forget(w: Lifted) -> Witness:
    return w.old


def actual_observation(w: Witness) -> tuple[object, ...]:
    # The model keeps the full linked observation, not just its flat support.
    return w.observe()


def independent_marginal_join(rows: set[tuple[int, int]]) -> set[tuple[int, int]]:
    left = {x for x, _ in rows}
    right = {y for _, y in rows}
    return {(x, y) for x in left for y in right}


def witnesses_for(rows: frozenset[tuple[int, int]], fiber: tuple[int, int, int]) -> set[Witness]:
    witnesses = set()
    for index, (arg, body) in enumerate(sorted(rows)):
        witnesses.add(
            Witness(
                fiber,
                arg,
                body,
                result=(arg ^ body),
                d_minus=f"d-minus-{index}",
                d_plus=f"d-plus-{index}",
                b_plus=f"b-plus-{index}",
            )
        )
    return witnesses


def powerset(items: tuple[tuple[int, int], ...]):
    for n in range(len(items) + 1):
        yield from (frozenset(xs) for xs in combinations(items, n))


def smallest_marginal_counterexample() -> tuple[set[tuple[int, int]], set[tuple[int, int]]]:
    universe = tuple((x, y) for x in range(2) for y in range(2))
    for rel in powerset(universe):
        source = set(rel)
        product = independent_marginal_join(source)
        if product != source:
            return source, product
    raise AssertionError("binary relation search unexpectedly found no counterexample")


def check_all_binary_relations() -> tuple[int, int]:
    universe = tuple((x, y) for x in range(2) for y in range(2))
    checked = 0
    marginal_failures = 0
    fiber = (3, 5, 8)  # fixed nu,K,D identifiers for each generated relation
    for rel in powerset(universe):
        source = witnesses_for(rel, fiber)
        lifted = {total_lift(w) for w in source}
        assert {forget(w) for w in lifted} == source
        assert {w.old.observe() for w in lifted} == {
            actual_observation(w) for w in source
        }
        assert all(
            w.d_projection == (w.old.arg_origin,)
            and w.b_projection == (w.old.body_origin, w.old.result)
            and w.flat_output == tuple(
                sorted(set(w.d_projection) | set(w.b_projection))
            )
            for w in lifted
        )
        # Distinct source occurrences keep their own evidence identities.
        source_ids = {
            (w.arg_origin, w.body_origin): (w.d_minus, w.d_plus, w.b_plus)
            for w in source
        }
        assert len(set(source_ids.values())) == len(source)
        assert all(
            (w.old.d_minus, w.old.d_plus, w.old.b_plus)
            == source_ids[(w.old.arg_origin, w.old.body_origin)]
            for w in lifted
        )
        rows = {(w.arg_origin, w.body_origin) for w in source}
        if independent_marginal_join(rows) != rows:
            marginal_failures += 1
        checked += 1
    return checked, marginal_failures


def main() -> None:
    checked, marginal_failures = check_all_binary_relations()
    minimal_source, spurious_join = smallest_marginal_counterexample()
    assert len(minimal_source) == 2
    assert len(spurious_join - minimal_source) == 2
    print(f"joint binary relations checked: {checked}")
    print("old-tuple total-coordinate lift: all projections and observations preserved")
    print(f"independent-marginal counterexamples: {marginal_failures}/{checked}")
    print(f"minimal correlated source rows: {sorted(minimal_source)}")
    print(f"spurious rows after marginal join: {sorted(spurious_join - minimal_source)}")
    print("scope: Theorem C §2.6 local lift invariant only; no source adequacy or Theorem C proof")


if __name__ == "__main__":
    main()
