#!/usr/bin/env python3
"""Exhaust the sharper callback hiding criterion, without a source claim.

Two old witnesses, one challenge and two complete observations suffice to
separate uniform admission, same-witness admission and observation coverage.
The checked and actual bounds are equal on checked-admitted fibers for the
exact linked lift. For arbitrary conservative checked bounds, coverage is
necessary only for preservation against *every* such checked completion.

Run: python3 tools/research_callback_admission_coverage.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


Z = range(2)
OBS = frozenset({0, 1})
SUBSETS = tuple(frozenset(o for o in OBS if mask & (1 << o)) for mask in range(4))
DOMAINS = tuple(product((False, True), repeat=2))
BOUNDS = tuple(product(SUBSETS, repeat=2))


@dataclass(frozen=True)
class Family:
    da: tuple[bool, bool]
    dc: tuple[bool, bool]
    pa: tuple[frozenset[int], frozenset[int]]
    pc: tuple[frozenset[int], frozenset[int]]


def union_on(domain, bounds) -> frozenset[int]:
    return frozenset(o for z in Z if domain[z] for o in bounds[z])


def pointwise(f: Family) -> bool:
    return all(not f.dc[z] or (f.da[z] and f.pa[z] <= f.pc[z]) for z in Z)


def exact_on_checked(f: Family) -> bool:
    return all(not f.dc[z] or f.pa[z] == f.pc[z] for z in Z)


def uniform(f: Family) -> bool:
    return f.dc[0] == f.dc[1]


def same_witness(f: Family) -> bool:
    return not any(f.dc) or all(
        not (f.da[z] and f.pa[z]) or f.dc[z] for z in Z
    )


def coverage(f: Family) -> bool:
    return not any(f.dc) or union_on(f.da, f.pa) <= union_on(f.dc, f.pa)


def marginal_comparison(f: Family) -> bool:
    # Deliberately compute the conclusion with checked bounds, not coverage's
    # restricted actual bounds. They coincide only under exact_on_checked.
    if any(f.dc) and not any(f.da):
        return False
    return not any(f.dc) or union_on(f.da, f.pa) <= union_on(f.dc, f.pc)


def encoding(f: Family) -> tuple[int, ...]:
    mask = lambda row: sum(1 << o for o in row)
    return (*map(int, f.da), *map(int, f.dc),
            *map(mask, f.pa), *map(mask, f.pc))


def cost(f: Family):
    # Count only active bound members; bits outside admission are encodings,
    # not members of either marginal contract.
    return (
        sum(f.da) + sum(f.dc),
        sum(len(f.pa[z]) * f.da[z] + len(f.pc[z]) * f.dc[z] for z in Z),
        encoding(f),
    )


def describe(f: Family) -> str:
    rows = lambda bs: tuple(tuple(sorted(b)) for b in bs)
    return f"DA={f.da}, DC={f.dc}, PA={rows(f.pa)}, PC={rows(f.pc)}"


def exhaust():
    counts = dict(encodings=0, pointwise=0, exact=0, uniform=0,
                  same_witness=0, coverage=0, preserved=0)
    examples: dict[str, list[Family]] = {
        "same-witness strictly weaker than uniform": [],
        "coverage strictly weaker than same-witness": [],
        "particular conservative completion needs no coverage": [],
        "exact linked lift fails without coverage": [],
        "inactive actual bound must be omitted": [],
    }
    for da, dc, pa, pc in product(DOMAINS, DOMAINS, BOUNDS, BOUNDS):
        f = Family(da, dc, pa, pc)
        counts["encodings"] += 1
        if not pointwise(f):
            continue
        counts["pointwise"] += 1
        h, s, r, p = uniform(f), same_witness(f), coverage(f), marginal_comparison(f)
        assert not h or s, f
        assert not s or r, f
        assert not r or p, f
        for name, holds in (("uniform", h), ("same_witness", s),
                            ("coverage", r), ("preserved", p)):
            counts[name] += int(holds)
        if exact_on_checked(f):
            counts["exact"] += 1
            assert r == p, f
            if not p:
                examples["exact linked lift fails without coverage"].append(f)
            if all(da) and s and not h and union_on(dc, pa):
                examples["same-witness strictly weaker than uniform"].append(f)
            if r and not s:
                examples["coverage strictly weaker than same-witness"].append(f)
        if p and not r:
            examples["particular conservative completion needs no coverage"].append(f)
        # Mutation: forgetting domain qualification invents observations from
        # old fibers where the challenge is not actual-admitted.
        unqualified = frozenset().union(*pa)
        if any(dc) and p and not unqualified <= union_on(dc, pc):
            examples["inactive actual bound must be omitted"].append(f)
    assert counts["encodings"] == 4096
    assert counts["pointwise"] == 1681
    assert counts["exact"] == 1296
    assert counts["uniform"] == 1105
    minima = {name: min(cases, key=cost) for name, cases in examples.items()}
    assert cost(minima["exact linked lift fails without coverage"])[:2] == (3, 1)
    return counts, minima


def exhaust_all_checked_completions() -> int:
    base_count = 0
    for da, dc, pa in product(DOMAINS, DOMAINS, BOUNDS):
        if any(dc[z] and not da[z] for z in Z):
            continue
        base_count += 1
        completions = [Family(da, dc, pa, pc) for pc in BOUNDS
                       if pointwise(Family(da, dc, pa, pc))]
        assert completions
        # This finite universal has a different quantifier from testing one
        # chosen conservative checked endpoint.
        all_preserved = all(marginal_comparison(f) for f in completions)
        minimum = Family(da, dc, pa, pa)
        assert pointwise(minimum)
        assert all_preserved == coverage(minimum), minimum
        if not coverage(minimum):
            assert not marginal_comparison(minimum), minimum
    assert base_count == 144
    return base_count


def whole_observation_erasure_example() -> None:
    # Here 0 and 1 specifically stand for quiet complete returns of int 0/1
    # in the same context, with no different request/authority coordinates.
    # The example does not authorize erasing distinct provider/request owners.
    raw = Family((True, True), (False, True),
                 (frozenset({0}), frozenset({1})),
                 (frozenset({0}), frozenset({1})))
    projected_bounds = tuple(frozenset(0 for _ in row) for row in raw.pa)
    projected = Family(raw.da, raw.dc, projected_bounds, projected_bounds)
    assert pointwise(raw) and exact_on_checked(raw)
    assert not coverage(raw) and not marginal_comparison(raw)
    assert coverage(projected) and marginal_comparison(projected)
    assert not same_witness(projected)


def main() -> None:
    counts, minima = exhaust()
    bases = exhaust_all_checked_completions()
    whole_observation_erasure_example()
    for name, count in counts.items():
        print(f"{name}: {count}")
    print(f"base families checked against every conservative completion: {bases}")
    for name, f in minima.items():
        print(f"{name}: cost={cost(f)[:2]}; {describe(f)}")
    print("whole-observation int erasure can establish coverage: confirmed")
    print("scope: finite relational encodings, not production endpoint semantics; "
          "unbounded results require the separate proofs")


if __name__ == "__main__":
    main()
