#!/usr/bin/env python3
"""Executable finite witness for the higher-order source-join obstruction.

The source is the exact identity specialization from
callback-coverage-and-source-joins.md §6.3: `f` returns the callable it was
given, then the returned callable is invoked. Two source owners have one
shared Function interface but distinct request origins and continuations.
This checks how a type-only stage join invents cross-owner histories, and how
retaining the original returned-provider incidence restores the exact join.

This is a relational source-core model, not a production endpoint denotation,
Function comparison, or principal-scheme proof.

Run: python3 tools/research_principal_higher_join.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations


CHALLENGES = ("h0", "h1")
PROVIDERS = ("g0", "g1")
INTERFACE = "Fun(Unit, e, Unit)"


@dataclass(frozen=True, order=True)
class SourceRow:
    challenge: str
    input_provider: str

    @property
    def returned_provider(self) -> str:
        # f y = y: the first call returns this exact source callable.
        return self.input_provider

    @property
    def request_origin(self) -> str:
        # The later invocation enters the returned provider.
        return f"request:{self.returned_provider}"

    @property
    def continuation(self) -> str:
        return f"continuation:{self.returned_provider}"


UNIVERSE = tuple(SourceRow(h, g) for h in CHALLENGES for g in PROVIDERS)


def powerset(items):
    for size in range(len(items) + 1):
        yield from (frozenset(xs) for xs in combinations(items, size))


def exact_projected_bound(rows: frozenset[SourceRow]):
    return frozenset((r.challenge, r.request_origin, r.continuation) for r in rows)


def joined_without_provider_incidence(rows: frozenset[SourceRow]):
    # Independent stage marginals share only the common printed Function
    # interface. The second invocation can therefore be paired with any first
    # stage challenge that admits that same interface.
    first = {(r.challenge, INTERFACE) for r in rows}
    second = {
        (INTERFACE, r.request_origin, r.continuation)
        for r in rows
    }
    return frozenset(
        (challenge, origin, continuation)
        for challenge, interface in first
        for right_interface, origin, continuation in second
        if interface == right_interface
    )


def joined_with_provider_incidence(rows: frozenset[SourceRow]):
    # Keep the existing returned callable as the shared source coordinate.
    first = {(r.challenge, r.returned_provider) for r in rows}
    second = {
        (r.returned_provider, r.request_origin, r.continuation)
        for r in rows
    }
    return frozenset(
        (challenge, origin, continuation)
        for challenge, provider in first
        for right_provider, origin, continuation in second
        if provider == right_provider
    )


def complexity(rows, spurious):
    return (len(rows), len(spurious), tuple(sorted(rows)))


def exhaust():
    cases = 0
    exact_join_cases = 0
    lossy_interface_join_cases = 0
    minimum = None
    for rows in powerset(UNIVERSE):
        exact = exact_projected_bound(rows)
        linked = joined_with_provider_incidence(rows)
        lossy = joined_without_provider_incidence(rows)
        assert linked == exact
        exact_join_cases += 1
        spurious = lossy - exact
        if spurious:
            lossy_interface_join_cases += 1
            candidate = (rows, exact, lossy, spurious)
            if minimum is None or complexity(rows, spurious) < complexity(
                minimum[0], minimum[3]
            ):
                minimum = candidate
        cases += 1
    assert cases == 16
    assert exact_join_cases == 16
    assert minimum is not None
    return cases, lossy_interface_join_cases, minimum


def main() -> None:
    cases, lossy_count, witness = exhaust()
    rows, exact, lossy, spurious = witness
    assert len(rows) == 2
    assert exact == frozenset({
        ("h0", "request:g0", "continuation:g0"),
        ("h1", "request:g1", "continuation:g1"),
    })
    assert len(lossy) == 4 and len(spurious) == 2
    assert ("h0", "request:g1", "continuation:g1") in spurious
    print(f"finite source challenge/provider relations checked: {cases}")
    print(f"provider-incidence joins equal exact source image: {cases}/{cases}")
    print(f"type-only stage join invents cross-owner histories: {lossy_count} relations")
    print(
        "minimum source: (h0,g0),(h1,g1); exact origins are diagonal; "
        "type-only join adds (h0,request:g1,continuation:g1)"
    )
    print(
        "scope: identity-returning higher-order source core and one later call; "
        "no solver, endpoint denotation, or principal common allowance"
    )


if __name__ == "__main__":
    main()
