#!/usr/bin/env python3
"""Exhaustive typed-pullback model of finite complete-contract joins.

This exercises the semantic contract join in
common-allowance-context-preimage.md §5 for a two-stage source tuple (g, x).
The first stage observes a Function-valued argument and the second an Int
argument. Their challenge domains are pulled back along separate projections;
their concrete event supports are joined at the same source tuple. A mutant
that intersects the raw local domains as if they were one challenge universe
loses the minimal two-stage source tuple.

This is finite semantic-contract characterization only. It does not model
Yulang's single `A <: B` resolver, coupled Function effect-port evidence,
abstract row components, subtraction attachments, or principal-scheme maps.

Run: python3 tools/research_principal_contract_join.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product


FUNCTION_VALUES = ("fn0", "fn1")
INT_VALUES = (0, 1)
EVENTS = ("Read", "Write")


def powerset(items):
    for size in range(len(items) + 1):
        yield from (frozenset(xs) for xs in combinations(items, size))


SUPPORTS = tuple(powerset(EVENTS))
FUNCTION_ROWS = tuple(product(SUPPORTS, repeat=len(FUNCTION_VALUES)))
INTEGER_ROWS = tuple(product(SUPPORTS, repeat=len(INT_VALUES)))
FUNCTION_DOMAINS = tuple(powerset(FUNCTION_VALUES))
INTEGER_DOMAINS = tuple(powerset(INT_VALUES))


@dataclass(frozen=True, order=True)
class SourceTuple:
    # The same outer source assignment relates both invocation stages.
    function_argument: str
    integer_argument: int


def source_relations():
    tuples = tuple(SourceTuple(f, x) for f, x in product(FUNCTION_VALUES, INT_VALUES))
    yield from powerset(tuples)


def pullback_domain(
    source: frozenset[SourceTuple],
    local_domain: frozenset,
    projection: str,
) -> frozenset[SourceTuple]:
    if projection == "function":
        return frozenset(t for t in source if t.function_argument in local_domain)
    if projection == "integer":
        return frozenset(t for t in source if t.integer_argument in local_domain)
    raise ValueError(projection)


def support_at(row: tuple[frozenset[str], ...], value) -> frozenset[str]:
    if isinstance(value, str):
        return row[FUNCTION_VALUES.index(value)]
    return row[INT_VALUES.index(value)]


def exhaust() -> tuple[int, int]:
    cases = 0
    nonempty_domains = 0
    for source, d_function, d_integer, p_function, p_integer in product(
        source_relations(),
        FUNCTION_DOMAINS,
        INTEGER_DOMAINS,
        FUNCTION_ROWS,
        INTEGER_ROWS,
    ):
        d_first = pullback_domain(source, d_function, "function")
        d_second = pullback_domain(source, d_integer, "integer")
        d_join = d_first & d_second
        if d_join:
            nonempty_domains += 1

        # The common contract keeps the complete source tuple and joins each
        # stage's support only after applying its own typed projection.
        joined = {
            t: support_at(p_function, t.function_argument)
            | support_at(p_integer, t.integer_argument)
            for t in d_join
        }

        # Each stage embeds in the join. For any flat concrete candidate row
        # that covers both stage views, it also covers their union (leastness).
        for t, common in joined.items():
            first = support_at(p_function, t.function_argument)
            second = support_at(p_integer, t.integer_argument)
            assert first <= common and second <= common
            for candidate in SUPPORTS:
                if first <= candidate and second <= candidate:
                    assert common <= candidate

        # Domain condition: every source tuple retained by a candidate common
        # contract must be admitted by both stage-local domains. Exhaust all
        # candidate source-tuple domains on this four-tuple universe.
        for candidate_domain in powerset(tuple(source)):
            candidate_domain = frozenset(candidate_domain)
            if candidate_domain <= d_first and candidate_domain <= d_second:
                assert candidate_domain <= d_join
            if candidate_domain <= d_join:
                assert candidate_domain <= d_first and candidate_domain <= d_second
        cases += 1

    # There are 16 source relations, 4 domains per stage, and 16 support maps
    # per stage: exhaustively cover the complete 65,536-case universe.
    assert cases == 16 * 4 * 4 * 16 * 16 == 65_536
    return cases, nonempty_domains


def minimal_raw_domain_mutant():
    # Minimize by source-tuple count, then local-domain sizes.
    for function_value in FUNCTION_VALUES:
        for integer_value in INT_VALUES:
            source = frozenset({SourceTuple(function_value, integer_value)})
            d_function = frozenset({function_value})
            d_integer = frozenset({integer_value})
            correct = pullback_domain(source, d_function, "function") & pullback_domain(
                source, d_integer, "integer"
            )
            # Wrongly using one raw common challenge set forces values of
            # distinct sorts to be equal.
            mutant = frozenset(
                t for t in source
                if t.function_argument == t.integer_argument
                and t.function_argument in d_function
                and t.integer_argument in d_integer
            )
            if correct and not mutant:
                return source, correct, mutant
    raise AssertionError("expected a typed-domain pullback counterexample")


def main() -> None:
    cases, nonempty = exhaust()
    source, correct, mutant = minimal_raw_domain_mutant()
    assert len(source) == 1 and len(correct) == 1 and not mutant
    print(f"complete finite contract joins checked: {cases}")
    print(f"cases with at least one source tuple in the joined domain: {nonempty}")
    print("typed-pullback domain condition and least flat-support join: pass")
    print(
        "minimal raw-domain intersection mutant: "
        f"source={tuple(source)}, typed join={tuple(correct)}, mutant={tuple(mutant)}"
    )
    print(
        "scope: two typed invocation projections and closed concrete support rows; "
        "no complete Function solver or scheme-instantiation theorem"
    )


if __name__ == "__main__":
    main()
