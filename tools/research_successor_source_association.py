#!/usr/bin/env python3
"""Research-only dependent-graph/slot-isomorphism discriminator.

This checks a finite representation claim, not source admission or Lic_C.
Call/Bind semantics and independent typing are supplied assumptions. No
parser, solver, Oracle, production endpoint, or successful comparison is used.
"""

from dataclasses import dataclass, replace
from itertools import permutations, product
import json
import resource
import time


@dataclass(frozen=True)
class Row:
    nu: int
    K: int
    D: int
    scope: str
    world: int
    entry: str
    callee_request: bool
    argument_request: bool
    body_request: bool
    consumer_request: bool


@dataclass(frozen=True)
class Contribution:
    """Index of a complete relational template, not one execution witness."""

    root: str
    xi: tuple
    scope: str
    entry: str
    stages: tuple
    request_suffixes: tuple


@dataclass(frozen=True)
class Incidence:
    slot: object
    beta: str
    upper: str
    position: str
    source_arm: str
    contribution: Contribution


def complete_family(row, upper):
    # The inert argument is received before provider-owned entry. For retained
    # entry, the body's explicit consumers are separate from an entry Force.
    stages = (("callee", row.callee_request), ("receipt", False))
    if row.entry == "Value":
        stages += (("entry-force", row.argument_request), ("rebind", False))
    else:
        stages += (("retain-carrier", False),)
    stages += (("body", row.body_request), ("native-return", False),
               ("designated-consumer", row.consumer_request),
               ("invocation-return", False))
    # A request stores the exact remaining source suffix. A response may use
    # either current world. This template retains a divergent/suspended prefix
    # without pretending it has reached Return/rebind.
    suffixes = tuple((stage, stages[index + 1:], (0, 1))
                     for index, (stage, request) in enumerate(stages) if request)
    return Contribution("Call:" + upper, (row.nu, row.K, row.D), row.scope,
                        row.entry, stages, suffixes)


def form(row):
    # Two source occurrences exercise representation invariance. This does
    # not assert that this source's original Slots inventory has two entries.
    return tuple(Incidence(("schema", upper), "beta:f", upper, "call.effect",
                           "OwnUpper", complete_family(row, upper))
                 for upper in ("u0", "u1"))


def independently_typed_row(row):
    # A supplied correlation-sensitive finite kernel. It is not a Yulang
    # typing/admission rule; its purpose is to make projection preserve a
    # genuine whole relation, including live K,D and the original scope.
    return (row.K == row.nu and row.D == (row.nu ^ row.world)
            and row.scope == "original")


def active_kernel(row, table):
    """Read contribution identity/typing through original active incidences."""
    if not independently_typed_row(row) or len(table) != 2:
        return False
    if len({inc.slot for inc in table}) != 2:
        return False
    for inc in table:
        if (inc.beta != "beta:f" or inc.source_arm != "OwnUpper"
                or inc.position != "call.effect"
                or inc.contribution != complete_family(row, inc.upper)):
            return False
    return {inc.upper for inc in table} == {"u0", "u1"}


def reencode(table, targets):
    bijection = dict(zip((inc.slot for inc in table), targets, strict=True))
    assert len(set(bijection.values())) == len(table)
    return tuple(replace(inc, slot=bijection[inc.slot]) for inc in table)


def view_events(contribution):
    # The callee prefix belongs to the full source Call. The receiver's upper
    # view begins at receipt; a complete-root index is not blanket attribution.
    return tuple(stage for stage, request in contribution.stages
                 if request and stage != "callee")


def main():
    started = time.monotonic()
    rows = tuple(Row(nu, K, D, "original", world, entry, cf, arg, body, consumer)
                 for nu, K, D, world, entry, cf, arg, body, consumer in
                 product((0, 1), (0, 1), (0, 1), (0, 1),
                         ("Value", "Computation"), (False, True),
                         (False, True), (False, True), (False, True)))
    original = {row for row in rows if independently_typed_row(row)}
    extended = {(row, form(row)) for row in rows if active_kernel(row, form(row))}
    assert {row for row, _ in extended} == original
    assert len(extended) == len(original)
    reencodings = 0
    for row, table in extended:
        for targets in permutations((31, 72)):
            encoded = reencode(table, targets)
            assert active_kernel(row, encoded)
            # Inversion recovers full original incidence, not the label alone.
            assert {(i.beta, i.upper, i.position, i.source_arm, i.contribution)
                    for i in table} == {
                        (i.beta, i.upper, i.position, i.source_arm, i.contribution)
                        for i in encoded}
            reencodings += 1

    quiet = Row(0, 0, 0, "original", 0, "Value", False, False, False, False)
    table = form(quiet)
    mutations = {}
    mutations["slot-collapse-is-not-isomorphism"] = not active_kernel(
        quiet, tuple(replace(i, slot=0) for i in table))
    mutations["source-position-is-not-contribution"] = not active_kernel(
        quiet, tuple(replace(i, contribution=i.position) for i in table))
    mutations["provider-retag-is-not-coherent-renaming"] = not active_kernel(
        quiet, tuple(replace(i, source_arm="InheritedProvider") for i in table))
    mutations["another-xi-is-not-the-original-fiber"] = not active_kernel(
        quiet, tuple(replace(i, contribution=replace(i.contribution, xi=(1, 1, 1)))
                     for i in table))
    mutations["younger-scope-is-not-original-binding"] = not active_kernel(
        quiet, tuple(replace(i, contribution=replace(i.contribution, scope="fresh"))
                     for i in table))
    rich = replace(quiet, argument_request=True, body_request=True,
                   consumer_request=True)
    rich_table = form(rich)
    mutations["body-only-loses-entry-and-consumer"] = not active_kernel(
        rich, tuple(replace(i, contribution=replace(i.contribution,
                     stages=(("body", True),), request_suffixes=()))
                    for i in rich_table))
    mutations["discarded-suffix-loses-relational-contribution"] = not active_kernel(
        rich, tuple(replace(i, contribution=replace(i.contribution,
                                                  request_suffixes=()))
                    for i in rich_table))
    prefix = complete_family(replace(quiet, callee_request=True), "u0")
    mutations["full-call-prefix-is-not-upper-view-event"] = (
        "callee" not in view_events(prefix)
        and any(stage == "callee" and request for stage, request in prefix.stages))
    assert all(mutations.values())
    print(json.dumps({"claim": "finite conditional representation check",
                      "candidate_rows": len(rows), "typed_rows": len(original),
                      "graph_extensions": len(extended),
                      "bijective_reencodings": reencodings,
                      "named_mutations_rejected": mutations,
                      "wall_seconds": round(time.monotonic() - started, 6),
                      "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},
                     sort_keys=True))


if __name__ == "__main__":
    main()
