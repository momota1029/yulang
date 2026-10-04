#!/usr/bin/env python3
"""Compare two candidate readings of a concrete effect-row component.

The model keeps each complete typed observation inside one fixed ``Rel_C``
fiber. Events retain identity, origin, source occurrence, family, typed family
arguments, port path, and whether they occur in a resumed/latent suffix. It
compares:

* port coverage: every compatible event in the complete port observation is
  covered by ``write int`` when its typed path reaches that port; and
* component-owned filtering: additionally require the event to be attached to
  the exact source occurrence assigned to the row component.

These are exploratory interpretations, not selected Yulang semantics. The
checker only establishes that they differ even when the event is in the same
complete observation and has a typed path to the same port. It does not model
the subtyping solver, general family variance, handler transitions, or derive
the annotation-to-occurrence rule.

Run: python3 tools/research_effect_component_membership.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True, order=True)
class Fiber:
    # One assignment and its joint witnesses are shared by all observations.
    nu: str
    k: str
    d: str


@dataclass(frozen=True, order=True)
class Event:
    event_id: str
    origin: str
    source_occurrence: str
    family: str
    family_argument: str
    port_path: str | None
    in_suffix: bool


@dataclass(frozen=True)
class CompleteObservation:
    fiber: Fiber
    challenge: str
    port: str
    events: tuple[Event, ...]


@dataclass(frozen=True)
class ConcreteComponent:
    occurrence: str
    family: str
    family_argument: str


def covered_by_port(component: ConcreteComponent, obs: CompleteObservation) -> bool:
    """Candidate: matching typed events on the complete port path are covered."""
    return any(
        event.family == component.family
        and event.family_argument == component.family_argument
        and event.port_path == obs.port
        for event in obs.events
    )


def covered_by_component_owned_event(
    component: ConcreteComponent, obs: CompleteObservation
) -> bool:
    """Candidate mutant: also require event ownership by this row item."""
    return any(
        event.family == component.family
        and event.family_argument == component.family_argument
        and event.port_path == obs.port
        and event.source_occurrence == component.occurrence
        for event in obs.events
    )


def event_universe(component: ConcreteComponent) -> tuple[Event, ...]:
    # Same-family/same-type events may originate at another expression; wrong
    # family/type and events with no path to the port are controls.
    return (
        Event("q0", "origin-A", component.occurrence, component.family,
              component.family_argument, "port", False),
        Event("q1", "origin-B", "other-occurrence", component.family,
              component.family_argument, "port", True),
        Event("q2", "origin-C", "other-occurrence", component.family,
              "other-type", "port", True),
        Event("q3", "origin-D", "other-occurrence", "read",
              component.family_argument, "port", True),
        Event("q4", "origin-E", "other-occurrence", component.family,
              component.family_argument, None, True),
    )


def check_same_fiber_observations() -> tuple[int, int, int]:
    fiber = Fiber("nu0", "K0", "D0")
    component = ConcreteComponent("annotation-occurrence", "write", "int")
    universe = event_universe(component)
    checks = differing = suffix_witnesses = 0

    # Every complete observation retains the exact same fiber; no projection
    # is recombined with a different K,D tuple during candidate comparison.
    for width in range(1, len(universe) + 1):
        for selection in product((False, True), repeat=len(universe)):
            events = tuple(event for event, keep in zip(universe, selection) if keep)
            if len(events) != width:
                continue
            obs = CompleteObservation(fiber, "challenge", "port", events)
            broad = covered_by_port(component, obs)
            owned = covered_by_component_owned_event(component, obs)
            assert not owned or broad
            if broad != owned:
                differing += 1
                assert any(
                    e.source_occurrence != component.occurrence
                    and e.family == component.family
                    and e.family_argument == component.family_argument
                    and e.port_path == obs.port
                    for e in obs.events
                )
            if any(e.in_suffix and e.family == component.family for e in events):
                suffix_witnesses += 1
            checks += 1

    # Minimal complete-history witness: the compatible event is in a resumed
    # suffix, reaches the same port, and is not owned by the row item's source
    # occurrence. Both interpretations keep its event/origin identity intact.
    q = Event("q1", "origin-B", "other-occurrence", "write", "int", "port", True)
    obs = CompleteObservation(fiber, "challenge", "port", (q,))
    assert covered_by_port(component, obs)
    assert not covered_by_component_owned_event(component, obs)
    assert (obs.fiber, obs.events[0].event_id, obs.events[0].origin) == (
        fiber, "q1", "origin-B"
    )
    assert checks == 2**len(universe) - 1
    return checks, differing, suffix_witnesses


def main() -> None:
    checks, differing, suffix_witnesses = check_same_fiber_observations()
    assert differing > 0 and suffix_witnesses > 0
    print(f"nonempty complete observations checked in one Rel_C fiber: {checks}")
    print(f"observations distinguishing the two readings: {differing}")
    print(f"observations retaining same-family suffix events: {suffix_witnesses}")
    print(
        "minimal distinction: a compatible same-family event on the complete "
        "port path is covered by port coverage, but rejected by component-owned filtering"
    )
    print(
        "scope: two candidate membership readings only; no handler semantics, "
        "annotation rule, solver relation, or production authority"
    )


if __name__ == "__main__":
    main()
