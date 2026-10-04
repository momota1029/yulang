#!/usr/bin/env python3
"""Exhaust the callback fixed-fiber hiding lemma and its missing-premise case.

Forgetting a source witness ``z`` after a fixed-fiber callback comparison is
safe when checked challenge admission is uniform across that forgotten fiber.
This checker exhausts the smallest nontrivial Boolean universe and also
shrinks a counterexample when that uniformity premise is removed.

Run: python3 tools/research_callback_admission_hiding.py
"""

from __future__ import annotations

from itertools import product


Z = (0, 1)
CHALLENGES = ("h",)
OBSERVATIONS = ("o",)
SUBSETS = tuple(range(1 << len(OBSERVATIONS)))
DOMAINS = tuple(range(1 << len(CHALLENGES)))


def has(mask: int, values: tuple, value) -> bool:
    return bool(mask & (1 << values.index(value)))


def members(mask: int, values: tuple) -> frozenset:
    return frozenset(value for bit, value in enumerate(values) if mask & (1 << bit))


def fixed_fiber_holds(da: tuple[int, ...], dc: tuple[int, ...],
                      pa: tuple[int, ...], pc: tuple[int, ...]) -> bool:
    for zi in range(len(Z)):
        for h in CHALLENGES:
            if has(dc[zi], CHALLENGES, h):
                if not has(da[zi], CHALLENGES, h):
                    return False
                if not members(pa[zi], OBSERVATIONS) <= members(pc[zi], OBSERVATIONS):
                    return False
    return True


def checked_admission_uniform(dc: tuple[int, ...]) -> bool:
    return all(
        has(dc[0], CHALLENGES, h) == has(dc[1], CHALLENGES, h)
        for h in CHALLENGES
    )


def projected_comparison_holds(da: tuple[int, ...], dc: tuple[int, ...],
                               pa: tuple[int, ...], pc: tuple[int, ...]) -> bool:
    domain_a = frozenset(
        h for h in CHALLENGES if any(has(row, CHALLENGES, h) for row in da)
    )
    domain_c = frozenset(
        h for h in CHALLENGES if any(has(row, CHALLENGES, h) for row in dc)
    )
    if not domain_c <= domain_a:
        return False
    for h in domain_c:
        bound_a = frozenset(
            obs
            for zi, row in enumerate(da)
            if has(row, CHALLENGES, h)
            for obs in members(pa[zi], OBSERVATIONS)
        )
        bound_c = frozenset(
            obs
            for zi, row in enumerate(dc)
            if has(row, CHALLENGES, h)
            for obs in members(pc[zi], OBSERVATIONS)
        )
        if not bound_a <= bound_c:
            return False
    return True


def all_cases():
    # Each domain and bound has 2 choices (one challenge and one observation).
    # Four z-indexed domain cells and four bound cells give 2^8 = 256 cases.
    return product(DOMAINS, DOMAINS, DOMAINS, DOMAINS,
                   SUBSETS, SUBSETS, SUBSETS, SUBSETS)


def unpack(case):
    da0, da1, dc0, dc1, pa0, pa1, pc0, pc1 = case
    return (da0, da1), (dc0, dc1), (pa0, pa1), (pc0, pc1)


def exhaustive_check() -> tuple[int, int, int, int]:
    total = fixed = uniform_fixed = 0
    uniform_projection = 0
    for case in all_cases():
        da, dc, pa, pc = unpack(case)
        total += 1
        if not fixed_fiber_holds(da, dc, pa, pc):
            continue
        fixed += 1
        if not checked_admission_uniform(dc):
            continue
        uniform_fixed += 1
        assert projected_comparison_holds(da, dc, pa, pc), case
        uniform_projection += 1
    assert total == 256
    assert uniform_projection == uniform_fixed
    return total, fixed, uniform_fixed, uniform_projection


def cost(case) -> tuple[int, int, tuple[int, ...]]:
    da, dc, pa, pc = unpack(case)
    active_domain_rows = sum(
        len(members(da[z], CHALLENGES)) + len(members(dc[z], CHALLENGES))
        for z in range(len(Z))
    )
    active_observations = sum(
        len(members(pa[z], OBSERVATIONS)) * len(members(da[z], CHALLENGES))
        + len(members(pc[z], OBSERVATIONS)) * len(members(dc[z], CHALLENGES))
        for z in range(len(Z))
    )
    return active_domain_rows, active_observations, tuple(case)


def minimum_nonuniform_counterexample():
    candidates = []
    for case in all_cases():
        da, dc, pa, pc = unpack(case)
        if (fixed_fiber_holds(da, dc, pa, pc)
                and not checked_admission_uniform(dc)
                and not projected_comparison_holds(da, dc, pa, pc)):
            candidates.append(case)
    if not candidates:
        raise AssertionError("expected the nonuniform-admission countermodel")
    return min(candidates, key=cost)


def main() -> None:
    total, fixed, uniform_fixed, uniform_projection = exhaustive_check()
    counterexample = minimum_nonuniform_counterexample()
    da, dc, pa, pc = unpack(counterexample)
    assert cost(counterexample)[:2] == (3, 1)
    assert len(members(da[0], CHALLENGES)) + len(members(da[1], CHALLENGES)) == 2
    assert len(members(dc[0], CHALLENGES)) + len(members(dc[1], CHALLENGES)) == 1
    assert fixed_fiber_holds(da, dc, pa, pc)
    assert not checked_admission_uniform(dc)
    assert not projected_comparison_holds(da, dc, pa, pc)
    print(f"fixed-fiber assignments checked: {total}")
    print(f"cases satisfying fixed-fiber comparison: {fixed}")
    print(
        "uniform checked-admission cases satisfying projected comparison: "
        f"{uniform_projection}/{uniform_fixed}"
    )
    print(
        "minimum nonuniform-admission projection failure "
        "(domain-membership count, active-observation count): "
        f"{cost(counterexample)[:2]}"
    )
    print(
        f"DA={tuple(members(row, CHALLENGES) for row in da)}, "
        f"DC={tuple(members(row, CHALLENGES) for row in dc)}, "
        f"PA={tuple(members(row, OBSERVATIONS) for row in pa)}, "
        f"PC={tuple(members(row, OBSERVATIONS) for row in pc)}"
    )
    print(
        "scope: two forgotten witnesses, one challenge, one observation; "
        "no production source derivation or endpoint generation"
    )


if __name__ == "__main__":
    main()
