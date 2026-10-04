#!/usr/bin/env python3
"""Check the higher-order boundary of the approved typed callback projection.

The finite source has an identity callback that returns an input callable, then
invokes that returned callable once. Two runtime callables share one structural
Function interface but carry distinct authority origins and continuations. The
approved projection may erase concrete scalar value identity; this model has
no scalar payload to erase, so callable authority and the subsequent typed
request remain visible.

The checker exhausts all nonempty candidate endpoint owner sets containing
the actual source owner. It confirms that complete projected membership factors through
the exact source graph iff no extra callable authority was admitted. A mutant
that drops authority labels makes those extra endpoint observations appear to
factor. This is a bounded obstruction to generalizing the integer `Sat_j`
abstraction to callable values, not a counterexample to the approved
projection or to production Yulang.

Run: python3 tools/research_callback_callable_projection.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations


FIBER = ("nu0", "K0", "D0")
SCOPE = "identity-callback-body"
CALL_PATH = "returned-function-call"
OPERATION_KIND = "Read"
OWNERS = ("owner-left", "owner-right")
INTERFACE = "Fun(Int, Read, Int)"


@dataclass(frozen=True, order=True)
class CallableValue:
    authority: str
    interface: str = INTERFACE


@dataclass(frozen=True, order=True)
class Observation:
    fiber: tuple[str, str, str]
    binder_scope: str
    typed_path: str
    # The result callable, later invoked by a distinct client occurrence.
    result_authority: str
    result_interface: str
    invocation_authority: str
    operation_kind: str
    request_origin: str
    continuation_owner: str


def invoke(value: CallableValue) -> Observation:
    # Both providers expose the same typed operation. Their authority and
    # continuation provenance remain distinct in the complete observation.
    return Observation(
        fiber=FIBER,
        binder_scope=SCOPE,
        typed_path=CALL_PATH,
        result_authority=value.authority,
        result_interface=value.interface,
        invocation_authority=value.authority,
        operation_kind=OPERATION_KIND,
        request_origin=f"request-from:{value.authority}",
        continuation_owner=f"continuation-of:{value.authority}",
    )


def source_identity_trace(source_argument: CallableValue) -> frozenset[Observation]:
    # Identity returns the exact input callable; the client's later use follows
    # that same source-owned descriptor and authority.
    return frozenset({invoke(source_argument)})


def endpoint_trace(admitted_result_owners: frozenset[str]) -> frozenset[Observation]:
    # This parameter deliberately stands for a candidate endpoint denotation;
    # the checker does not claim the production solver admits any particular set.
    return frozenset(invoke(CallableValue(owner)) for owner in admitted_result_owners)


def typed_observation(observation: Observation) -> tuple[object, ...]:
    """The approved projection's retained fields in this callable-only case."""
    return (
        observation.fiber,
        observation.binder_scope,
        observation.typed_path,
        observation.result_authority,
        observation.result_interface,
        observation.invocation_authority,
        observation.operation_kind,
        observation.request_origin,
        observation.continuation_owner,
    )


def authority_erasing_mutant(observation: Observation) -> tuple[object, ...]:
    """Wrongly treat function values as erased scalar data."""
    return (
        observation.fiber,
        observation.binder_scope,
        observation.typed_path,
        "<callable-erased>",
        observation.result_interface,
        "<invocation-owner-erased>",
        observation.operation_kind,
        "<request-origin-erased>",
        "<continuation-owner-erased>",
    )


def subsets(items: tuple[str, ...]):
    for size in range(len(items) + 1):
        yield from (frozenset(xs) for xs in combinations(items, size))


def exhaust() -> tuple[int, int, tuple[str, frozenset[str], Observation]]:
    cases = 0
    real_failures = 0
    false_green_cases = 0
    minimal = None
    for source_owner in OWNERS:
        source_argument = CallableValue(source_owner)
        source = {typed_observation(x) for x in source_identity_trace(source_argument)}
        source_erased = {
            authority_erasing_mutant(x)
            for x in source_identity_trace(source_argument)
        }
        for admitted in subsets(OWNERS):
            if source_owner not in admitted:
                continue
            endpoint = endpoint_trace(admitted)
            endpoint_typed = {typed_observation(x) for x in endpoint}
            endpoint_erased = {authority_erasing_mutant(x) for x in endpoint}

            factors = endpoint_typed <= source
            expected = admitted == frozenset({source_owner})
            assert factors == expected
            if not factors:
                real_failures += 1
                extra = next(x for x in endpoint if typed_observation(x) not in source)
                if minimal is None or (len(admitted), source_owner, tuple(sorted(admitted))) < (
                    len(minimal[1]), minimal[0], tuple(sorted(minimal[1]))
                ):
                    minimal = (source_owner, admitted, extra)

            mutant_factors = endpoint_erased <= source_erased
            if mutant_factors and not factors:
                false_green_cases += 1
            cases += 1

    assert cases == 4  # two source owners times two supersets containing each
    assert real_failures == 2
    assert false_green_cases == 2
    assert minimal is not None
    return cases, false_green_cases, minimal


def main() -> None:
    cases, false_green_cases, witness = exhaust()
    source_owner, admitted, extra = witness
    assert source_owner == "owner-left"
    assert admitted == frozenset(OWNERS)
    assert extra.result_authority == "owner-right"
    assert extra.request_origin == "request-from:owner-right"
    print(f"candidate callable endpoint cases checked: {cases}")
    print("complete projected factorization agrees with source ownership: pass")
    print(f"authority-erasing mutant false-green cases: {false_green_cases}")
    print(
        "minimal extra witness: source owner=owner-left, endpoint admits both "
        "same-interface owners, extra returned/invoked owner=owner-right, "
        "request origin=request-from:owner-right"
    )
    print(
        "scope: one returned callable and one future invocation; scalar identity, "
        "general latent histories, and production endpoint denotation are not modeled"
    )


if __name__ == "__main__":
    main()
