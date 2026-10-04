#!/usr/bin/env python3
"""Check support projection after attachment-indexed partial subtraction.

This finite model separates three facts that a family-set row would collapse:

1. an effect point `(family, arguments)` occurs in the complete output view;
2. an individual dynamic event is attached to a concrete source contribution;
3. a particular handler invocation consumes that event before it reaches the
   output view.

Subtraction removes an event only from the event paths witnessed as consumed.
The public support point can be removed only if no same-point event remains in
the complete output image. This characterizes a necessary support-level
condition; it does not define annotation membership or handler semantics.

Run: python3 tools/research_effect_attachment_subtraction.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product

from research_mixed_effect_subtraction import (
    Event as ShallowEvent,
    shallow_resume_once,
)


@dataclass(frozen=True, order=True)
class EffectPoint:
    family: str
    arguments: str


@dataclass(frozen=True, order=True)
class Event:
    event_id: str
    origin: str
    point: EffectPoint
    attached_to_target: bool
    consumed_by_boundary: bool
    reaches_complete_output: bool


TARGET = EffectPoint("write", "int")
OTHER = EffectPoint("read", "unit")


def complete_output(events: tuple[Event, ...]) -> tuple[Event, ...]:
    """Preserve event identity while dropping only witnessed consumed paths."""
    return tuple(
        event
        for event in events
        if event.reaches_complete_output
        and not (event.attached_to_target and event.consumed_by_boundary)
    )


def support(events: tuple[Event, ...]) -> frozenset[EffectPoint]:
    return frozenset(event.point for event in events)


def enumerate_two_event_histories() -> tuple[int, int, int]:
    # One fixed (nu,K,D) fiber is implicit for every generated history. The
    # event coordinates vary; joint witnesses and assignments do not.
    checked = unsafe_family_deletions = duplicate_support_cases = 0
    for p0, p1 in product((TARGET, OTHER), repeat=2):
        for flags in product((False, True), repeat=6):
            attached0, attached1, consumed0, consumed1, output0, output1 = flags
            events = (
                Event("q0", "origin-0", p0, attached0, consumed0, output0),
                Event("q1", "origin-1", p1, attached1, consumed1, output1),
            )
            outgoing = complete_output(events)
            out_support = support(outgoing)

            # Only attached and boundary-consumed paths are subtracted. Every
            # surviving event keeps its full event/origin/family identity.
            for event in outgoing:
                assert not (event.attached_to_target and event.consumed_by_boundary)
                assert event in events

            # At support level, eliminating a concrete family/type point is
            # sound exactly when the complete output image has no such event.
            can_remove_target = TARGET not in out_support
            if any(
                event.point == TARGET
                and event.attached_to_target
                and event.consumed_by_boundary
                for event in events
            ) and TARGET in out_support:
                unsafe_family_deletions += 1
                assert not can_remove_target

            if any(e.point == TARGET for e in outgoing) and len(
                [e for e in outgoing if e.point == TARGET]
            ) > 1:
                duplicate_support_cases += 1
                assert len(out_support) == len(set(e.point for e in outgoing))
            checked += 1

    # 2 points per event, 6 independent evidence/output bits per pair.
    assert checked == 2 * 2 * 2**6 == 256
    return checked, unsafe_family_deletions, duplicate_support_cases


def minimal_same_family_survivor() -> tuple[Event, ...]:
    # q0 is the attached contribution consumed by the boundary. q1 is a
    # distinct same-family event reaching output from another source path.
    events = (
        Event("q0", "origin-0", TARGET, True, True, False),
        Event("q1", "origin-1", TARGET, False, False, True),
    )
    outgoing = complete_output(events)
    assert tuple(e.event_id for e in outgoing) == ("q1",)
    assert support(outgoing) == frozenset({TARGET})
    return outgoing


def differential_shallow_projection() -> int:
    """Compare attachment projection with the separate 96-history model."""
    families = ("tick", "write")
    checked = 0
    for length in (2, 3):
        for family_vector in product(families, repeat=length):
            history = tuple(
                ShallowEvent(i, family, "same-source-flow")
                for i, family in enumerate(family_vector)
            )
            target = EffectPoint(history[0].family, "opaque-args")
            for resume, outer_mask in product((False, True), range(1 << len(families))):
                outer = frozenset(
                    family
                    for i, family in enumerate(families)
                    if outer_mask & (1 << i)
                )
                reference = shallow_resume_once(
                    history,
                    selected_family=history[0].family,
                    resume_raw_continuation=resume,
                    outer_consumes=outer,
                )
                projected_input = tuple(
                    Event(
                        f"q{event.event_id}",
                        event.origin,
                        EffectPoint(event.family, "opaque-args"),
                        attached_to_target=event.family == target.family,
                        consumed_by_boundary=event.event_id == 0,
                        reaches_complete_output=(
                            event.event_id != 0
                            and resume
                            and event.family not in outer
                        ),
                    )
                    for event in history
                )
                projected = complete_output(projected_input)
                assert tuple(
                    (int(event.event_id[1:]), event.point.family, event.origin)
                    for event in projected
                ) == tuple((event.event_id, event.family, event.origin) for event in reference)
                checked += 1
    assert checked == 96
    return checked


def main() -> None:
    checked, unsafe, duplicates = enumerate_two_event_histories()
    witness = minimal_same_family_survivor()
    differential = differential_shallow_projection()
    assert unsafe > 0 and duplicates > 0
    print(f"two-event attachment/output histories checked: {checked}")
    print(f"histories where consumed attachment does not justify support deletion: {unsafe}")
    print(f"histories with duplicate events but set-like public support: {duplicates}")
    print(f"differential shallow-projection histories: {differential}")
    print(
        "minimal witness: q0 is consumed; distinct same-family q1 reaches the "
        f"complete output image, retaining support {sorted((p.family, p.arguments) for p in support(witness))}"
    )
    print(
        "scope: necessary support-projection condition only; no annotation "
        "membership or handler source rule"
    )


if __name__ == "__main__":
    main()
