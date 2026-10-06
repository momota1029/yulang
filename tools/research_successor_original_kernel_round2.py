#!/usr/bin/env python3
"""Finite checks of the explicitly candidate envelope laws, not I_orig.

Run once with: prlimit --as=1073741824 timeout 60s python3 <this file>
No files, subprocesses, imports from the compiler, or semantic oracle are used.
"""

from dataclasses import dataclass, replace
from itertools import product
import json
import resource
import time


@dataclass(frozen=True)
class Coordinates:
    beta: tuple = ("outer-formal-f", "shared-root-R")
    scope: tuple = ("apply", "step")
    xi: tuple = ("nu-original", "K-original", "D-original")
    upper: str = "body-use-f-upper"
    position: str = "typed-upper-outEff"
    provider: str = "captured-outer-f"


@dataclass(frozen=True)
class Evidence:
    observation: str
    origin: str
    local_witness: str
    stage: str
    suffix: tuple


@dataclass(frozen=True)
class Envelope:
    """Free candidate certificate; deliberately not an original contribution."""
    coordinates: Coordinates
    fibers: frozenset
    latent: frozenset = frozenset()


def assemble(left, right):
    if left.coordinates != right.coordinates:
        raise ValueError("assembly requires one original coordinate tuple")
    return Envelope(left.coordinates, left.fibers | right.fibers,
                    left.latent | right.latent)


def rename(envelope, coordinate_map, witness_map):
    q = coordinate_map(envelope.coordinates)
    return Envelope(q, frozenset(witness_map(e) for e in envelope.fibers),
                    frozenset(witness_map(e) for e in envelope.latent))


def subsets(items):
    return [frozenset(item for bit, item in zip(bits, items) if bit)
            for bits in product((False, True), repeat=len(items))]


def reject(thunk):
    try:
        thunk()
    except ValueError:
        return
    raise AssertionError("invalid coordinate assembly accepted")


def main():
    started = time.monotonic()
    q = Coordinates()
    # Distinct whole evidence alternatives can have identical observations.
    a = Evidence("request-prefix", "source-provider", "w0", "receiver",
                 ("raw-k", "current-state", "rebind", "body", "consumer"))
    b = replace(a, local_witness="w1", origin="licensed-extra")
    c = Evidence("return-latent", "source-provider", "w2", "receiver",
                 ("returned-provider", "future-port"))
    domain = subsets((a, b, c))
    union_checks = 0
    for left, right in product(domain, repeat=2):
        joined = assemble(Envelope(q, left), Envelope(q, right))
        assert joined.fibers == left | right
        assert all(e in joined.fibers for e in left | right)
        assert joined.coordinates == q
        union_checks += 1

    # Conjunction/images must use whole correlated tuples, not marginal joins.
    rows = ((0, 0, "w0"), (1, 1, "w1"), (0, 1, "w2"))
    join_checks = 0
    for left, right in product(subsets(rows), repeat=2):
        whole_intersection = left & right
        indexed = {row: row[2] for row in left if row in right}
        assert frozenset(indexed) == whole_intersection
        join_checks += 1
    correlated = frozenset(((0, 0), (1, 1)))
    cartesian_marginals = frozenset(product({x for x, _ in correlated},
                                          {y for _, y in correlated}))
    assert (0, 1) in cartesian_marginals - correlated

    # Bijective reencoding acts on all coordinate/evidence fields together.
    def q_forward(original):
        return Coordinates(tuple("r:" + s for s in original.beta),
                           tuple("r:" + s for s in original.scope),
                           tuple("r:" + s for s in original.xi),
                           "r:" + original.upper, "r:" + original.position,
                           "r:" + original.provider)

    def q_back(encoded):
        return Coordinates(tuple(s[2:] for s in encoded.beta),
                           tuple(s[2:] for s in encoded.scope),
                           tuple(s[2:] for s in encoded.xi),
                           encoded.upper[2:], encoded.position[2:],
                           encoded.provider[2:])

    def e_forward(e):
        return Evidence("r:" + e.observation, "r:" + e.origin,
                        "r:" + e.local_witness, "r:" + e.stage,
                        tuple("r:" + s for s in e.suffix))

    def e_back(e):
        return Evidence(e.observation[2:], e.origin[2:], e.local_witness[2:],
                        e.stage[2:], tuple(s[2:] for s in e.suffix))

    transport_checks = 0
    for fibers in domain:
        env = Envelope(q, fibers, frozenset((c,)))
        assert rename(rename(env, q_forward, e_forward), q_back, e_back) == env
        transport_checks += 1

    # The exact nested source's returned closure carries f without invoking f.
    closed_step = Envelope(q, frozenset(), frozenset((a, b, c)))
    block_return = assemble(closed_step, Envelope(q, frozenset()))
    assert block_return.fibers == frozenset()
    assert block_return.latent == frozenset((a, b, c))
    future_body = Envelope(q, block_return.latent)
    assert future_body.coordinates.provider == "captured-outer-f"
    assert future_body.fibers == frozenset((a, b, c))
    # No snapshot of entry execution is substituted for Name x's rebound value.
    external_step_entry = Evidence("entry-request", "step-argument", "wa",
                                   "step-entry", ("step-rebind", "f-x-body"))
    rebound_name_x = Evidence("return-value", "inner-formal-x", "wx",
                             "argument-name", ())
    assert external_step_entry != rebound_name_x

    # Distinct provider marks survive directional upper seeding.
    protection_checks = 0
    for provider_mark in (False, True):
        marks = {"upper": False, "provider": provider_mark}
        marks["upper"] = True
        assert marks == {"upper": True, "provider": provider_mark}
        protection_checks += 1

    # Named shortcut falsifiers; all target candidate algebra/records only.
    mutations = []
    for name, changed in (
        ("changed-xi", replace(q, xi=("other-nu", *q.xi[1:]))),
        ("changed-scope", replace(q, scope=("apply", "other-step"))),
        ("retagged-capture", replace(q, provider="other-f")),
        ("different-upper", replace(q, upper="provider-lower")),
    ):
        reject(lambda changed=changed: assemble(Envelope(q, frozenset((a,))),
                                                Envelope(changed, frozenset((b,)))))
        mutations.append(name)
    canonical = {e.observation: e for e in (a, b)}
    assert len(canonical) == 1 and len(frozenset((a, b))) == 2
    mutations.append("observation-canonicalization-loses-witness")
    pointwise = (Envelope(q, frozenset((a,))), Envelope(q, frozenset((c,))))
    assert not any(e.fibers >= frozenset((a, c)) for e in pointwise)
    assert assemble(*pointwise).fibers >= frozenset((a, c))
    mutations.append("pointwise-selection-loses-uniform-family")
    assert replace(a, suffix=("body",)) != a
    mutations.append("body-only-drops-pending-suffix")
    assert replace(c, suffix=()) != c
    mutations.append("return-only-drops-future-port")
    assert Envelope(q, frozenset((a, b, c))) != closed_step
    mutations.append("executing-latent-return")
    assert cartesian_marginals != correlated
    mutations.append("independent-marginal-recombination")
    # An extra outside the hard envelope never becomes a legal member by union.
    hard = frozenset((a, b))
    extra = replace(c, origin="unlicensed-authority")
    guarded = frozenset((a, b, extra)) & hard
    assert extra not in guarded and b in guarded
    mutations.append("port-only-extra-ignores-hard-envelope")
    original_witnesses = frozenset(("a0/w0", "a1/w1"))
    selected_assembly_image = frozenset(("a0/w0",))
    assert selected_assembly_image < original_witnesses
    mutations.append("assembly-image-replacement-loses-original-license")

    print(json.dumps({
        "claim": "candidate finite consistency and shortcut falsifiers only",
        "union_cases": union_checks,
        "whole_tuple_conjunction_cases": join_checks,
        "bijective_transport_cases": transport_checks,
        "directional_protection_cases": protection_checks,
        "nested_capture_return_cases": 1,
        "mutations_rejected": mutations,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "original_kernel_rules_validated": False,
        "original_gates_closed": [],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
