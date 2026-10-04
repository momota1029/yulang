#!/usr/bin/env python3
"""Finite characterization of event identity under shallow raw resumption.

This is not a Function descriptor interpretation or an inference solver. It
characterizes one bounded consequence of the selected source-machine rule:
handling the first eligible request does not keep the selected shallow handler
around the raw continuation when the arm resumes it once.

The generated histories are fixed. Every event comes from one source flow;
the first request is assumed eligible and selected; its response permits one
raw-continuation resumption. `outer_consumes` is deliberately only a terminal
family filter: it suppresses matching suffix events and adds no requests,
state dependence, guards, or resumption. Actual outer-handler images are
outside this model.
"""

from dataclasses import dataclass
from itertools import product


@dataclass(frozen=True)
class Event:
    event_id: int
    family: str
    origin: str


def shallow_resume_once(
    events: tuple[Event, ...],
    *,
    selected_family: str,
    resume_raw_continuation: bool,
    outer_consumes: frozenset[str],
) -> tuple[Event, ...]:
    """Apply the bounded selected-first, one-resumption transition."""
    if not events or events[0].family != selected_family:
        forwarded = events
    elif resume_raw_continuation:
        forwarded = events[1:]
    else:
        forwarded = ()
    return tuple(event for event in forwarded if event.family not in outer_consumes)


def support(events: tuple[Event, ...]) -> frozenset[str]:
    return frozenset(event.family for event in events)


def check_bounded_model_consistency() -> int:
    checked = 0
    families = ("tick", "write")

    # Enumerate small ordered histories. Dynamic IDs differ while source-flow
    # origin is shared, matching repeated events from one computation.
    for length in (2, 3):
        for family_vector in product(families, repeat=length):
            # Repeated dynamic events may share one source-flow origin.
            events = tuple(
                Event(i, family, "same-source-flow")
                for i, family in enumerate(family_vector)
            )
            first = events[0]
            for resume in (False, True):
                for outer_mask in range(1 << len(families)):
                    outer = frozenset(
                        family
                        for i, family in enumerate(families)
                        if outer_mask & (1 << i)
                    )
                    output = shallow_resume_once(
                        events,
                        selected_family=first.family,
                        resume_raw_continuation=resume,
                        outer_consumes=outer,
                    )

                    # The selected dynamic event is consumed. A suffix event
                    # may have the same origin and family as that event.
                    assert all(e.event_id != first.event_id for e in output)
                    # Origin is source-flow identity and may remain shared;
                    # only the dynamic event identity is consumed here.
                    assert all(e.origin == first.origin for e in output)

                    # Every retained suffix event preserves its identity and
                    # origin. This fixture does not model attachment evidence.
                    expected = tuple(
                        e
                        for e in (events[1:] if resume else ())
                        if e.family not in outer
                    )
                    assert output == expected
                    checked += 1

    # Minimal distinguishing witness for support-only global cancellation.
    witness = (
        Event(0, "tick", "one-source-flow"),
        Event(1, "tick", "one-source-flow"),
    )
    image = shallow_resume_once(
        witness,
        selected_family="tick",
        resume_raw_continuation=True,
        outer_consumes=frozenset(),
    )
    input_support = support(witness)
    family_cancelled = input_support - {"tick"}

    assert image == (witness[1],)
    assert image[0].event_id != witness[0].event_id
    assert image[0].origin == witness[0].origin
    assert support(image) == frozenset({"tick"})
    assert family_cancelled == frozenset()
    assert support(image) != family_cancelled
    return checked


if __name__ == "__main__":
    print(f"checked {check_bounded_model_consistency()} bounded model cases")
    print("minimized witness: same-family suffix survives; family cancellation erases it")
