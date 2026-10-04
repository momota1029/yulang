#!/usr/bin/env python3
"""Check source-selected capture eligibility for a concrete effect item.

The governing ordinary-computation design records the user's decision that a
concrete callback contract gives equal eligibility to direct requests and
caller-owned requests exposed by ``Force`` in the same complete ``CallView``.
Eligibility still requires the exact operation contract, typed observation
path/incidence, and live receiver/handler. Origin alone is not authority, and
family equality alone is not sufficient.

This finite matrix is a consistency check for that selected rule. It contrasts
it with a deliberately wrong source-occurrence filter and a family-only
predicate. It does not derive source annotation elaboration, mixed abstract /
concrete component membership, handler semantics, or the ``A <: B`` solver.

Run: python3 tools/research_effect_component_membership.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True, order=True)
class Fiber:
    nu: str
    k: str
    d: str


@dataclass(frozen=True, order=True)
class ConcreteContract:
    annotation_occurrence: str
    port: str
    family: str
    family_argument: str


@dataclass(frozen=True, order=True)
class EventView:
    event_id: str
    origin: str
    origin_occurrence: str
    family: str
    family_argument: str
    observed_port: str | None
    typed_path_incidence: bool
    receiver_active: bool
    handler_active: bool
    in_later_force_suffix: bool


def selected_capture_rule(contract: ConcreteContract, event: EventView) -> bool:
    """User-selected rule: exact typed contract + observed live incidence."""
    return (
        event.family == contract.family
        and event.family_argument == contract.family_argument
        and event.observed_port == contract.port
        and event.typed_path_incidence
        and event.receiver_active
        and event.handler_active
    )


def wrong_origin_filter(contract: ConcreteContract, event: EventView) -> bool:
    """Mutant: wrongly require event origin to equal annotation occurrence."""
    return (
        selected_capture_rule(contract, event)
        and event.origin_occurrence == contract.annotation_occurrence
    )


def wrong_family_only_rule(contract: ConcreteContract, event: EventView) -> bool:
    """Mutant: wrongly infer capture from family/type equality alone."""
    return (
        event.family == contract.family
        and event.family_argument == contract.family_argument
    )


def enumerate_fixed_fiber() -> tuple[int, int, int, int]:
    fiber = Fiber("nu0", "K0", "D0")
    contract = ConcreteContract("annotation-occurrence", "callview-port", "write", "int")
    checks = eligible = origin_mutant_differences = family_only_false_positives = 0

    for origin, family, argument, observed, path, receiver, handler, suffix in product(
        ("direct", "caller-force"),
        ("write", "read"),
        ("int", "unit"),
        (False, True),
        (False, True),
        (False, True),
        (False, True),
        (False, True),
    ):
        event = EventView(
            event_id="q0",
            origin=origin,
            origin_occurrence=(
                "annotation-occurrence" if origin == "direct" else "caller-thunk-occurrence"
            ),
            family=family,
            family_argument=argument,
            observed_port="callview-port" if observed else None,
            typed_path_incidence=path,
            receiver_active=receiver,
            handler_active=handler,
            in_later_force_suffix=suffix,
        )

        # All rows refer to the exact same complete typed-assignment fiber;
        # only the bounded event-view coordinates vary.
        assert fiber == Fiber("nu0", "K0", "D0")
        actual = selected_capture_rule(contract, event)
        owner_mutant = wrong_origin_filter(contract, event)
        family_mutant = wrong_family_only_rule(contract, event)
        eligible += actual
        origin_mutant_differences += actual != owner_mutant
        family_only_false_positives += family_mutant and not actual

        assert not actual or (
            event.family == contract.family
            and event.family_argument == contract.family_argument
            and event.observed_port == contract.port
            and event.typed_path_incidence
            and event.receiver_active
            and event.handler_active
        )
        if origin == "direct":
            paired = EventView(
                **{
                    **event.__dict__,
                    "origin": "caller-force",
                    "origin_occurrence": "caller-thunk-occurrence",
                }
            )
            assert selected_capture_rule(contract, event) == selected_capture_rule(
                contract, paired
            )
        checks += 1

    # Two origins × two families × two arguments × five Boolean dimensions.
    assert checks == 2 * 2 * 2 * 2**5 == 256
    assert eligible == 4  # one per origin and suffix state
    assert origin_mutant_differences == 2
    assert family_only_false_positives > 0
    return checks, eligible, origin_mutant_differences, family_only_false_positives


def main() -> None:
    checks, eligible, origin_differences, family_false_positives = enumerate_fixed_fiber()
    print(f"typed capture views checked in one Rel_C fiber: {checks}")
    print(f"eligible exact-contract views: {eligible}")
    print(f"direct-vs-caller-Force origin-filter mutant failures: {origin_differences}")
    print(f"family-only false-positive views: {family_false_positives}")
    print(
        "scope: consistency with selected callback visibility; source annotation "
        "profile elaboration and mixed-row membership remain open"
    )


if __name__ == "__main__":
    main()
