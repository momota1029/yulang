#!/usr/bin/env python3
"""Finite support-projection stress model for principal common allowances.

This checks only the powerset-level consequence of the acceptance criteria:
several distinct invocation/branch supports can share their least public
allowance without identifying the original supports. It is not an effect-row
subtyping relation, Function comparison, source generator, or principality
proof. All source occurrences stay in an ordered tuple throughout the model.

Run: python3 tools/research_principal_support.py
"""

from __future__ import annotations

from itertools import combinations, product


def powerset(items: tuple[int, ...]):
    for n in range(len(items) + 1):
        yield from (frozenset(xs) for xs in combinations(items, n))


def least_common_allowance(rows: tuple[frozenset[int], ...]) -> frozenset[int]:
    return frozenset().union(*rows)


def factors_through(rows: tuple[frozenset[int], ...], allowance: frozenset[int]) -> bool:
    # Each original occurrence is checked directly; rows are never equated.
    return all(row <= allowance for row in rows)


def check(universe_size: int, max_occurrences: int) -> tuple[int, int]:
    supports = tuple(powerset(tuple(range(universe_size))))
    cases = 0
    distinct_endpoint_cases = 0
    for count in range(1, max_occurrences + 1):
        for rows in product(supports, repeat=count):
            rows = tuple(rows)
            least = least_common_allowance(rows)
            assert factors_through(rows, least)
            for candidate in supports:
                # The candidate allowance admits every original endpoint iff
                # it admits their least common support.
                assert factors_through(rows, candidate) == (least <= candidate)
            # No multiplicity is added to the public support, but each use is
            # still represented separately in the source tuple.
            assert len(rows) == count
            if len(set(rows)) > 1:
                distinct_endpoint_cases += 1
                assert len(least) <= sum(map(len, rows))
            cases += 1
    return cases, distinct_endpoint_cases


def minimal_distinct_rows() -> tuple[tuple[frozenset[int], ...], frozenset[int]]:
    universe = tuple(range(2))
    supports = tuple(powerset(universe))
    candidates = []
    for count in range(2, 4):
        for rows in product(supports, repeat=count):
            least = least_common_allowance(rows)
            if len(set(rows)) > 1 and all(row != least for row in rows):
                candidates.append((count, sum(map(len, rows)), rows))
        if candidates:
            break
    _, _, rows = min(candidates, key=lambda x: (x[0], x[1], x[2]))
    return rows, least_common_allowance(rows)


def main() -> None:
    cases, distinct = check(universe_size=3, max_occurrences=3)
    rows, allowance = minimal_distinct_rows()
    assert len(rows) == 2
    assert len(set(rows)) == 2
    assert allowance != rows[0] and allowance != rows[1]
    print(f"finite support assignments checked: {cases}")
    print(f"assignments retaining distinct occurrence supports: {distinct}")
    print(f"minimal distinct endpoints: {tuple(map(sorted, rows))}")
    print(f"least common public support: {sorted(allowance)}")
    print("scope: finite support factorization only; no source, Function, or principal-scheme theorem")


if __name__ == "__main__":
    main()
