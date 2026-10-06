#!/usr/bin/env python3
"""Finite characterization of the 2026-10-06 user-selected directional rule.

Not a compiler, a source parser, a complete effect semantics, or independent
proof review. Both algorithms below implement the same displayed local rule.
Only source-certified protected-variable exposures are within its envelope.
Run: python3 tools/research_directional_protection.py
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import combinations, product
from typing import FrozenSet, Iterable, Tuple

ASSERTIONS = 0


@dataclass(frozen=True)
class Seed:
    origin: str
    root: str
    scope: str


@dataclass(frozen=True)
class Bound:
    occurrence: str
    direction: str             # upper: v <: Fun; lower: Fun <: v
    root: str
    scope: str
    effect: str                # covariant effect endpoint, NOT an effect set
    argument: str = "a"
    input_effect: str = "b"
    result: str = "d"
    source_generated: bool = True
    protected_origins: FrozenSet[str] = frozenset()

    def __post_init__(self) -> None:
        if self.direction not in ("upper", "lower"):
            raise ValueError("bound direction must be upper or lower")


@dataclass(frozen=True)
class Incidence:
    origin: str
    root: str
    scope: str
    occurrence: str
    path: str
    endpoint: str


def seed_for_binding(origin: str, root: str, scope: str, *,
                     inferred_formal: bool, annotation_absent: bool) -> Tuple[Seed, ...]:
    """The selected unannotated higher-order formal case, not every bare name.

    inferred_formal is an independently resolved source classification;
    this test helper does not infer it from spelling or a solved type.
    """
    if inferred_formal and annotation_absent:
        return (Seed(origin, root, scope),)
    return ()


def reference(seeds: Iterable[Seed], bounds: Iterable[Bound]) -> FrozenSet[Incidence]:
    """Literal introduction-rule comprehension, with no relation-closure step."""
    seeds, bounds = tuple(seeds), tuple(bounds)
    return frozenset(
        Incidence(s.origin, s.root, s.scope, b.occurrence, "call.effect", b.effect)
        for s in seeds for b in bounds
        if (b.direction == "upper" and b.source_generated
            and s.origin in b.protected_origins
            and (s.root, s.scope) == (b.root, b.scope))
    )


def indexed(seeds: Iterable[Seed], bounds: Iterable[Bound]) -> FrozenSet[Incidence]:
    """A separate indexed join, not independent source-semantics validation."""
    table: dict[tuple[str, str], set[str]] = {}
    for s in seeds:
        table.setdefault((s.root, s.scope), set()).add(s.origin)
    out: set[Incidence] = set()
    seen: dict[str, Bound] = {}
    for b in bounds:
        old = seen.get(b.occurrence)
        if old is not None and old != b:
            raise ValueError("one occurrence ID was assigned incompatible source records")
        seen[b.occurrence] = b
        if b.direction != "upper" or not b.source_generated:
            continue
        for origin in table.get((b.root, b.scope), ()):
            if origin not in b.protected_origins:
                continue
            out.add(Incidence(origin, b.root, b.scope, b.occurrence,
                              "call.effect", b.effect))
    return frozenset(out)


def subsets(xs: Tuple) -> Iterable[Tuple]:
    for size in range(len(xs) + 1):
        yield from combinations(xs, size)


def assert_equal(actual: object, expected: object, label: str) -> None:
    global ASSERTIONS
    ASSERTIONS += 1
    if actual != expected:
        raise AssertionError(f"{label}: actual={actual!r}, expected={expected!r}")


def check_examples() -> dict[str, int]:
    start = ASSERTIONS
    s = Seed("no-annotation:f", "f", "outer")
    u = Bound("use:f(x)", "upper", "f", "outer", "c",
              protected_origins=frozenset({s.origin}))
    lo = Bound("recursive-provider", "lower", "f", "outer", "g")
    expected = frozenset({Incidence(s.origin, "f", "outer", u.occurrence,
                                    "call.effect", "c")})
    assert_equal(indexed((s,), (lo, u)), expected, "lower before upper")
    assert_equal(indexed((s,), (u, lo)), expected, "lower after upper")
    assert_equal(indexed((s,), (lo,)), frozenset(), "lower is not a producer")
    assert_equal(indexed((), (u,)), frozenset(), "unprotected root")
    assert_equal(seed_for_binding("external", "g", "outer", inferred_formal=False,
                                 annotation_absent=True), (), "bare external name")
    assert_equal(seed_for_binding("f", "f", "outer", inferred_formal=True,
                                 annotation_absent=False), (), "not the no-annotation rule")
    assert_equal(indexed((s,), (replace(u, scope="other"),)), frozenset(), "scope")
    assert_equal(indexed((s,), (replace(u, source_generated=False),)), frozenset(),
                 "pending comparison alone")
    assert_equal(indexed((s,), (replace(u, protected_origins=frozenset()),)), frozenset(),
                 "missing protected-variable premise")
    # An arbitrary late seed is NOT justified by this test. Permutations below
    # reorder existing certified records, not semantic source stages.
    assert_equal(indexed((s,), (u, u)), expected, "replay idempotence")
    later = replace(s, origin="another-seed")
    assert_equal(indexed((s, later), (u,)), expected, "seed-specific exposure premise")
    for result in ("Int", "Thunk(io,Int)", "Fun(Unit,io,Int)", "mu t.Thunk(io,t)"):
        assert_equal(indexed((s,), (replace(u, result=result),)), expected,
                     "no whole-result shape traversal")
    # Equal solved endpoint values do not identify original upper/lower ports.
    same_endpoint = replace(lo, effect="c")
    assert_equal(indexed((s,), (u, same_endpoint)), expected, "endpoint alias")
    second = replace(u, occurrence="use:f(y)")
    actual = indexed((s,), (u, second))
    assert_equal(len(actual), 2, "distinct uses share an endpoint, not an incidence")
    inherited = Incidence("independent-provider", "f", "outer", lo.occurrence,
                          "call.effect", "g")
    assert_equal(indexed((s,), (u, lo)) | {inherited}, expected | {inherited},
                 "keep independently inherited protection")
    try:
        indexed((s,), (u, replace(u, direction="lower")))
    except ValueError:
        pass
    else:
        raise AssertionError("incompatible occurrence identity was accepted")
    return {"focused_equalities": ASSERTIONS - start, "invalid_identity_rejections": 1}


def exhaustive_join() -> dict[str, int]:
    seeds = tuple(Seed(f"seed:{i}", f"v{i}", "S") for i in range(3))
    checked = 0
    for endpoint_bits in product(range(2), repeat=3):
        ups = tuple(Bound(f"u{i}:{j}", "upper", f"v{i}", "S",
                          f"effect{endpoint_bits[i]}",
                          protected_origins=frozenset({f"seed:{i}"}))
                    for i in range(3) for j in range(2))
        lows = tuple(Bound(f"lo{i}", "lower", f"v{i}", "S",
                           f"effect{endpoint_bits[i]}") for i in range(3))
        for ss in subsets(seeds):
            for uu in subsets(ups):
                expected = reference(ss, uu)
                for ll in subsets(lows):
                    bs = ll + uu
                    actual = indexed(ss, bs)
                    assert_equal(actual, expected, "exhaustive direction/alias join")
                    assert_equal(indexed(reversed(ss), reversed(bs)), expected,
                                 "certified-record enumeration order")
                    checked += 1
    return {"join_instances": checked, "order_checks": checked}


def joint_lift() -> dict[str, int]:
    # All relations on the SAME three Boolean coordinates, not actual source
    # admissibility or a production nu,K,D definition.
    universe = tuple(product(range(2), repeat=3))
    families = 0
    for relation in subsets(universe):
        lifted = {(row, ("source-u", "call.effect", row[1])) for row in relation}
        assert_equal({row for row, _ in lifted}, set(relation), "same-tuple erasure")
        # A pending query is a later filter, never a generator input.
        for q in (lambda r: True, lambda r: r[0] == r[1], lambda r: r[2] == 0):
            after = {(r, witness) for r, witness in lifted if q(r)}
            assert_equal({r for r, _ in after}, {r for r in relation if q(r)},
                         "unchanged pending-query predicate")
        families += 1
    diagonal = {(0, 0), (1, 1)}
    wrong = set(product({r[0] for r in diagonal}, {r[1] for r in diagonal}))
    if wrong == diagonal:
        raise AssertionError("marginal product mutant was not discriminated")
    return {"joint_relations": families, "query_filters": 3 * families,
            "joint_marginal_mutants_rejected": 1}


def mutation_checks() -> dict[str, int]:
    s = Seed("s", "f", "S")
    u = Bound("u", "upper", "f", "S", "c", protected_origins=frozenset({"s"}))
    lo = Bound("lo", "lower", "f", "S", "g")
    good = indexed((s,), (lo, u))
    all_inc = lambda b: Incidence("s", "f", "S", b.occurrence, "call.effect", b.effect)
    mutants = {
        "reverse_lower": good | {all_inc(lo)},
        "input_effect_instead": frozenset({replace(next(iter(good)), endpoint="b")}),
        "blanket_result": good | {Incidence("s", "f", "S", "u", "result.latent.effect", "io")},
        "erase_origin": frozenset({replace(next(iter(good)), origin="")}),
        "drop_required_upper": frozenset(),
    }
    for name, result in mutants.items():
        if result == good:
            raise AssertionError(f"mutant survived: {name}")
    two = indexed((s,), (u, replace(u, occurrence="u2")))
    collapsed = {(x.root, x.endpoint) for x in two}
    if len(collapsed) == len(two):
        raise AssertionError("endpoint-only incidence collapse mutant survived")
    # Rename all scoped coordinates coherently; source occurrence IDs stay original.
    ren_s = replace(s, root="fresh-f", scope="fresh-S")
    ren_u = replace(u, root="fresh-f", scope="fresh-S", effect="fresh-c")
    expected = frozenset(replace(x, root="fresh-f", scope="fresh-S", endpoint="fresh-c")
                         for x in good)
    assert_equal(indexed((ren_s,), (ren_u,)), expected, "joint alpha renaming")
    return {"named_mutants_rejected": len(mutants) + 1, "renaming_checks": 1}


def main() -> None:
    import json
    counts: dict[str, int] = {}
    for check in (check_examples, exhaustive_join, joint_lift, mutation_checks):
        counts.update(check())
    print(json.dumps({"status": "PASS", **counts}, sort_keys=True))


if __name__ == "__main__":
    main()
