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


@dataclass(frozen=True, order=True)
class BoundWitness:
    """A finite source bind derivation with its shared intermediate value."""

    fiber: int
    owner_pair: tuple[str, str]
    binder_scope: str
    argument: int
    intermediate: int
    result: int
    d_minus_id: str
    d_plus_id: str
    b_plus_id: str
    call_receipt: str
    argument_receipt: str


@dataclass(frozen=True, order=True)
class BoundLift:
    old: BoundWitness
    # Derived paths are computed only after first/suffix share one old tuple.
    linked_paths: tuple[tuple[str, int, int], ...]


def total_lift(w: Witness) -> Lifted:
    d = (w.arg_origin,)
    b = (w.body_origin, w.result)
    return Lifted(w, d, b, tuple(sorted(set(d) | set(b))))


def bind_relation(
    first: frozenset[tuple[int, int, int]],
    suffix: frozenset[tuple[int, int, int]],
    context: str,
) -> set[BoundWitness]:
    """Natural composition on the same fiber and intermediate value."""
    output = set()
    for fiber, argument, intermediate in first:
        for suffix_fiber, suffix_intermediate, result in suffix:
            if fiber != suffix_fiber or intermediate != suffix_intermediate:
                continue
            output.add(
                BoundWitness(
                    fiber=fiber,
                    owner_pair=(f"{context}:outer-owner-{fiber}", f"{context}:latent-owner-{fiber}"),
                    binder_scope=f"{context}:scope-{fiber}",
                    argument=argument,
                    intermediate=intermediate,
                    result=result,
                    d_minus_id=f"{context}:d-minus-{fiber}",
                    d_plus_id=f"{context}:d-plus-{fiber}",
                    b_plus_id=f"{context}:b-plus-{fiber}",
                    call_receipt=f"{context}:call-receipt-{fiber}",
                    argument_receipt=f"{context}:argument-receipt-{fiber}",
                )
            )
    return output


def lift_bind(rows: set[BoundWitness]) -> set[BoundLift]:
    return {
        BoundLift(
            row,
            (
                (row.d_minus_id, row.argument, row.intermediate),
                (row.d_plus_id, row.argument, row.intermediate),
                (row.b_plus_id, row.intermediate, row.result),
            ),
        )
        for row in rows
    }


def forget_bind(rows: set[BoundLift]) -> set[BoundWitness]:
    return {row.old for row in rows}


def bind_projection(row: BoundWitness) -> tuple[object, ...]:
    return (
        row.fiber,
        row.owner_pair,
        row.binder_scope,
        row.argument,
        row.intermediate,
        row.result,
        row.d_minus_id,
        row.d_plus_id,
        row.b_plus_id,
        row.call_receipt,
        row.argument_receipt,
    )


def bad_bind_dropping_intermediate(
    first: frozenset[tuple[int, int, int]],
    suffix: frozenset[tuple[int, int, int]],
) -> set[tuple[int, int, int]]:
    """Mutant: forget the shared intermediate before joining the children."""
    output = set()
    for fiber, argument, _intermediate in first:
        for suffix_fiber, _suffix_intermediate, result in suffix:
            if fiber == suffix_fiber:
                output.add((fiber, argument, result))
    return output


def find_minimal_bind_correlation_failure(require_nonempty: bool):
    first_universe = tuple((fiber, arg, mid) for fiber in range(2) for arg in range(2) for mid in range(2))
    suffix_universe = tuple((fiber, mid, result) for fiber in range(2) for mid in range(2) for result in range(2))
    for total_size in range(2, 5):
        for first_size in range(1, total_size):
            suffix_size = total_size - first_size
            if first_size > len(first_universe) or suffix_size > len(suffix_universe):
                continue
            for first_rows in combinations(first_universe, first_size):
                first = frozenset(first_rows)
                for suffix_rows in combinations(suffix_universe, suffix_size):
                    suffix = frozenset(suffix_rows)
                    actual = bind_relation(first, suffix, "minimum")
                    if require_nonempty and not actual:
                        continue
                    exact_projection = {
                        (row.fiber, row.argument, row.result) for row in actual
                    }
                    mutant = bad_bind_dropping_intermediate(first, suffix)
                    if mutant - exact_projection:
                        return first, suffix, exact_projection, mutant
    raise AssertionError("expected bind marginalization counterexample")


def check_bind_compositions() -> tuple[int, int]:
    first_universe = tuple((fiber, arg, mid) for fiber in range(2) for arg in range(2) for mid in range(2))
    suffix_universe = tuple((fiber, mid, result) for fiber in range(2) for mid in range(2) for result in range(2))
    first_relations = tuple(powerset(first_universe))
    suffix_relations = tuple(powerset(suffix_universe))
    cases = 0
    nonempty = 0
    for context in ("ctx-a", "ctx-b"):
        for first in first_relations:
            for suffix in suffix_relations:
                actual = bind_relation(first, suffix, context)
                checked = lift_bind(actual)
                assert forget_bind(checked) == actual
                assert {x.old for x in checked} == actual
                assert {bind_projection(x) for x in actual} == {
                    bind_projection(x.old) for x in checked
                }
                assert all(
                    item.linked_paths
                    == (
                        (item.old.d_minus_id, item.old.argument, item.old.intermediate),
                        (item.old.d_plus_id, item.old.argument, item.old.intermediate),
                        (item.old.b_plus_id, item.old.intermediate, item.old.result),
                    )
                    for item in checked
                )
                assert all(
                    item.old.call_receipt != item.old.argument_receipt
                    and item.old.owner_pair[0] != item.old.owner_pair[1]
                    for item in checked
                )
                if actual:
                    nonempty += 1
                cases += 1
    return cases, nonempty


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
    bind_cases, nonempty_bind_cases = check_bind_compositions()
    empty_first, empty_suffix, empty_exact, empty_mutant = find_minimal_bind_correlation_failure(
        require_nonempty=False
    )
    first, suffix, exact_bind, mutant_bind = find_minimal_bind_correlation_failure(
        require_nonempty=True
    )
    assert len(empty_first) + len(empty_suffix) == 2
    assert not empty_exact and empty_mutant
    assert len(first) + len(suffix) == 3
    assert exact_bind and mutant_bind - exact_bind
    print(f"joint binary relations checked: {checked}")
    print("old-tuple total-coordinate lift: all projections and observations preserved")
    print(f"independent-marginal counterexamples: {marginal_failures}/{checked}")
    print(f"minimal correlated source rows: {sorted(minimal_source)}")
    print(f"spurious rows after marginal join: {sorted(spurious_join - minimal_source)}")
    print(
        "finite bind relation pairs checked: "
        f"{bind_cases // 2} per metadata context across 2 contexts "
        f"({nonempty_bind_cases // 2} nonempty per context)"
    )
    print(
        "minimal bind mismatch (empty exact join): "
        f"first={sorted(empty_first)}, suffix={sorted(empty_suffix)}, "
        f"spurious={sorted(empty_mutant - empty_exact)}"
    )
    print(f"minimal bind mismatch with nonempty exact join: first={sorted(first)}, suffix={sorted(suffix)}")
    print(f"exact bind projection: {sorted(exact_bind)}")
    print(f"spurious after dropping shared intermediate: {sorted(mutant_bind - exact_bind)}")
    print("scope: finite total-lift and bind-shaped join checks only; no operational bind, source adequacy, or Theorem C proof")


if __name__ == "__main__":
    main()
