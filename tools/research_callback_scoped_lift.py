#!/usr/bin/env python3
"""Exhaustive scope-preservation probe for the callback checked lift.

The source-side relation uses one captured witness ``s`` outside a rigid
challenge ``kappa`` and an arm-local witness ``z`` inside it. The checked lift
adds a total coordinate ``w=t(s,kappa,z)`` at the same local scope. This model
does not generate Yulang endpoints; it tests the old-tuple-preserving lift
against finite quantifier-scope mutations that existing callback playgrounds
explicitly leave open.

Run: python3 tools/research_callback_scoped_lift.py
"""

from __future__ import annotations

from itertools import product


S_VALUES = (0, 1)
KAPPAS = (0, 1)
Z_VALUES = (0, 1)
W_VALUES = (0, 1)
OLD_TUPLES = tuple(product(S_VALUES, KAPPAS, Z_VALUES))
RELATIONS = tuple(
    frozenset(row for bit, row in enumerate(OLD_TUPLES) if mask & (1 << bit))
    for mask in range(1 << len(OLD_TUPLES))
)
TOTAL_MAPS = tuple(
    {row: (mask >> bit) & 1 for bit, row in enumerate(OLD_TUPLES)}
    for mask in range(1 << len(OLD_TUPLES))
)


def source_admits(relation: frozenset[tuple[int, int, int]], s: int) -> bool:
    """exists z-arm per rigid kappa, with s kept outside the rigid binder."""
    return all(any((s, kappa, z) in relation for z in Z_VALUES) for kappa in KAPPAS)


def checked_admits(
    relation: frozenset[tuple[int, int, int]],
    total_map: dict[tuple[int, int, int], int],
    s: int,
) -> bool:
    """Add a fresh total coordinate without moving any original binder."""
    return all(
        any(
            (s, kappa, z) in relation
            and any(
                w == total_map[(s, kappa, z)]
                for w in W_VALUES
            )
            for z in Z_VALUES
        )
        for kappa in KAPPAS
    )


def admits_with_capture_freshened(
    relation: frozenset[tuple[int, int, int]],
) -> bool:
    """Mutant: existentially choose captured s independently for each kappa."""
    return all(
        any((s, kappa, z) in relation for s in S_VALUES for z in Z_VALUES)
        for kappa in KAPPAS
    )


def admits_with_arm_witness_hoisted(
    relation: frozenset[tuple[int, int, int]], s: int
) -> bool:
    """Mutant: demand one z witness for all rigid kappa instances."""
    return any(
        all((s, kappa, z) in relation for kappa in KAPPAS)
        for z in Z_VALUES
    )


def admits_with_checked_coordinate_hoisted(
    relation: frozenset[tuple[int, int, int]],
    total_map: dict[tuple[int, int, int], int],
    s: int,
) -> bool:
    """Mutant: demand one w even when its source tuple varies with kappa."""
    return any(
        all(
            any(
                (s, kappa, z) in relation
                and total_map[(s, kappa, z)] == w
                for z in Z_VALUES
            )
            for kappa in KAPPAS
        )
        for w in W_VALUES
    )


def minimize_capture_mutant():
    # Minimize by relation cardinality, then mask order.
    for size in range(len(OLD_TUPLES) + 1):
        for mask, relation in enumerate(RELATIONS):
            if len(relation) != size:
                continue
            if any(source_admits(relation, s) for s in S_VALUES):
                continue
            if admits_with_capture_freshened(relation):
                return relation
    raise AssertionError("expected captured-witness scope counterexample")


def minimize_arm_mutant():
    for size in range(len(OLD_TUPLES) + 1):
        for relation in RELATIONS:
            if len(relation) != size:
                continue
            for s in S_VALUES:
                if source_admits(relation, s) and not admits_with_arm_witness_hoisted(relation, s):
                    return relation, s
    raise AssertionError("expected arm-witness scope counterexample")


def minimize_coordinate_mutant():
    for size in range(len(OLD_TUPLES) + 1):
        for relation in RELATIONS:
            if len(relation) != size:
                continue
            for total_map in TOTAL_MAPS:
                for s in S_VALUES:
                    if source_admits(relation, s) and not admits_with_checked_coordinate_hoisted(
                        relation, total_map, s
                    ):
                        return relation, total_map, s
    raise AssertionError("expected checked-coordinate scope counterexample")


def exhaust_lift() -> tuple[int, int]:
    pairs = nonempty = 0
    for relation, total_map in product(RELATIONS, TOTAL_MAPS):
        for s in S_VALUES:
            original = source_admits(relation, s)
            lifted = checked_admits(relation, total_map, s)
            assert lifted == original, (relation, total_map, s)
            nonempty += original
        pairs += 1
    assert pairs == 256 * 256 == 65_536
    return pairs, nonempty


def main() -> None:
    pairs, admitted_captured_assignments = exhaust_lift()
    capture_failure = minimize_capture_mutant()
    arm_failure, arm_s = minimize_arm_mutant()
    coordinate_failure, coordinate_map, coordinate_s = minimize_coordinate_mutant()
    assert len(capture_failure) == 2
    assert len(arm_failure) == 2
    assert len(coordinate_failure) == 2
    assert all(source_admits(capture_failure, s) is False for s in S_VALUES)
    assert admits_with_capture_freshened(capture_failure)
    assert source_admits(arm_failure, arm_s)
    assert not admits_with_arm_witness_hoisted(arm_failure, arm_s)
    assert source_admits(coordinate_failure, coordinate_s)
    assert not admits_with_checked_coordinate_hoisted(
        coordinate_failure, coordinate_map, coordinate_s
    )
    print(f"relation/total-coordinate maps checked: {pairs}")
    print(
        "old captured-tuple admission preserved under correctly scoped total lift: "
        f"pass ({admitted_captured_assignments} admitted (relation,map,s) triples)"
    )
    print(f"minimum captured-witness-scope mutant: {sorted(capture_failure)}")
    print(f"minimum arm-witness-hoisting mutant at s={arm_s}: {sorted(arm_failure)}")
    print(
        "minimum checked-coordinate-hoisting mutant at "
        f"s={coordinate_s}: relation={sorted(coordinate_failure)}, "
        f"total-map={coordinate_map}"
    )
    print(
        "scope: one fixed fiber and one typed observation; no source generation, "
        "endpoint denotation, Function comparison, or challenge-domain adequacy"
    )


if __name__ == "__main__":
    main()
