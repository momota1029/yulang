#!/usr/bin/env python3
"""Finite probe for projecting handler-local provenance to an `'e?` edge.

Two same-family events have distinct provenance: one arrives through input
component `e`, the other is an independent contribution. The fixed
boundary-order filter admits a contribution for capture only when that event
has typed incidence to the candidate boundary and the boundary's own contract
admits its concrete operation. The filter is evaluated independently per
event. An eligible event is removed from this candidate result image;
other events remain. This is not ordinary handler dispatch: receiver-body
visibility, shallow activation exit/unwind, and resumed suffix execution are
not modeled. The checker stipulates that the remaining support is observed
after receiver exit as ordinary output.

This checks whether family support alone determines the input-to-result edge,
and whether retaining that edge separates the finite cases. It is a
characterization of the Draft `'e?` reading, not source-machine proof,
principal-scheme semantics, or production code.

Run: python3 tools/research_handler_provenance_projection.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


FAMILY = "foo"
INNER = "inner"
OUTER = "receiver"
BOUNDARIES = (INNER, OUTER)  # fixed order for the candidate incidence filter


@dataclass(frozen=True, order=True)
class Event:
    event_id: str
    component: str  # `e` or independent/local
    operation: str
    typed_incidence: frozenset[str]


@dataclass(frozen=True)
class History:
    events: tuple[Event, ...]


@dataclass(frozen=True)
class Result:
    support: frozenset[str]
    input_edge: bool
    output_events: tuple[str, ...]
    filtered_at: tuple[tuple[str, str], ...]


def project(history: History) -> Result:
    output = []
    filtered = []
    input_edge = False
    for event in history.events:
        selected = next(
            (
                boundary
                for boundary in BOUNDARIES
                if boundary in event.typed_incidence
                and event.operation == FAMILY
            ),
            None,
        )
        if selected is not None:
            filtered.append((event.event_id, selected))
            continue
        output.append(event.event_id)
        if event.component == "e":
            input_edge = True
    support = frozenset(
        event.operation for event in history.events if event.event_id in output
    )
    return Result(support, input_edge, tuple(output), tuple(filtered))


def histories():
    incidence_sets = incidence_options()
    for input_incidence, local_incidence in product(incidence_sets, repeat=2):
        yield History(
            (
                Event("q-input", "e", FAMILY, input_incidence),
                Event("q-local", "local", FAMILY, local_incidence),
            )
        )


def family_only_projection(result: Result) -> frozenset[str]:
    return result.support


def support_plus_edge_projection(result: Result) -> tuple[frozenset[str], bool]:
    return result.support, result.input_edge


def incidence_options() -> tuple[frozenset[str], ...]:
    return tuple(
        frozenset(
            boundary
            for bit, boundary in enumerate(BOUNDARIES)
            if mask & (1 << bit)
        )
        for mask in range(1 << len(BOUNDARIES))
    )


def check() -> tuple[
    int,
    tuple[History, Result, History, Result],
    tuple[History, Result, History, Result],
]:
    rows = [(history, project(history)) for history in histories()]
    assert len(rows) == 16
    assert all(row.support <= {FAMILY} for _, row in rows)

    collision = None
    for i, (left_h, left) in enumerate(rows):
        for right_h, right in rows[i + 1 :]:
            if family_only_projection(left) == family_only_projection(right):
                if left.input_edge != right.input_edge:
                    collision = left_h, left, right_h, right
                    break
        if collision:
            break
    assert collision is not None

    # Adding the edge coordinate separates the minimized support collision.
    left_h, left, right_h, right = collision
    assert support_plus_edge_projection(left) != support_plus_edge_projection(right)
    assert left.support == right.support == frozenset({FAMILY})
    assert {left.input_edge, right.input_edge} == {False, True}

    # The globally smallest collision compares two one-event histories with
    # different source components but the same concrete operation instance.
    singletons = []
    for component in ("e", "local"):
        for mask, incidence in enumerate(incidence_options()):
            history = History(
                (Event(f"q-{component}-{mask}", component, FAMILY, incidence),)
            )
            singletons.append((history, project(history)))
    singleton_collision = next(
        (
            left_h,
            left,
            right_h,
            right,
        )
        for i, (left_h, left) in enumerate(singletons)
        for right_h, right in singletons[i + 1 :]
        if left.support == right.support and left.input_edge != right.input_edge
    )
    assert (
        singleton_collision[1].support
        == singleton_collision[3].support
        == frozenset({FAMILY})
    )
    assert {
        singleton_collision[1].input_edge,
        singleton_collision[3].input_edge,
    } == {False, True}
    return len(rows), singleton_collision, collision


def main() -> None:
    count, (single_lh, single_l, single_rh, single_r), (
        left_h,
        left,
        right_h,
        right,
    ) = check()
    print(f"ordered boundary-filter incidence assignments checked: {count}")
    print("family-support projection merges distinct input-to-result edges: confirmed")
    print(f"smallest one-event provenance collision: {single_lh.events} -> {single_l}")
    print(f"                                      and {single_rh.events} -> {single_r}")
    print(f"minimal support collision: {left_h.events} -> {left}")
    print(f"                       and {right_h.events} -> {right}")
    print("retaining the candidate edge separates these histories: confirmed")
    print("scope: two same-family events, two ordered incidence filters, one fixed fiber; "
          "no grammar, production evidence, solver, or principality theorem")


if __name__ == "__main__":
    main()
