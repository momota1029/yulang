#!/usr/bin/env python3
"""Finite source-order probe for annotation-free compose hygiene.

The model composes a caller-owned request exposed by Force(D_g) with the
Value-entry suffix RebindResultPath; B_f using the ordinary state-threaded
Request bind. It checks that an unannotated `f` handler cannot consume this
request solely because its operation occurs in the shared printed effect
component `b`. The source has no explicit callback-capture contract, so the
request's origin, event identity, fiber, and typed path remain visible in the
complete call and contribute to the outward covariant support `c`.

The matcher mutant subtracts the request when the component name matches and
the inner handler covers its operation. This is a proof-search counterexample
to inferring capture/subtraction from row-variable reuse. It is not a complete
Function solver, general source evaluator, or production endpoint theorem.

Run: python3 tools/research_compose_hygiene.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product


OPERATIONS = ("Read", "Write")
VALUES = (0, 1)
STATES = (0, 1)
FIBER = ("nu-compose", "K-compose", "D-compose")
ORIGIN = "request-origin:g-x"
EVENT_ID = "event:g-x:0"
TYPED_PATH = "J_arg:g-to-f"
SHARED_COMPONENT = "b"


@dataclass(frozen=True, order=True)
class Request:
    operation: str
    origin: str
    event_id: str
    fiber: tuple[str, str, str]
    typed_path: str
    responses: frozenset[tuple[int, int]]


@dataclass(frozen=True, order=True)
class BoundTrace:
    request: Request
    phase: str
    pending_suffix: tuple[str, ...]
    response: int | None
    live_state: int


@dataclass(frozen=True)
class ForcePrefix:
    completed_events: tuple[Request, ...]
    pending_event: Request | None
    live_state: int
    suffix: tuple[str, ...]


def powerset(items: tuple):
    for size in range(len(items) + 1):
        yield from (frozenset(xs) for xs in combinations(items, size))


RESPONSES = tuple(powerset(tuple(product(VALUES, STATES))))
HANDLER_SETS = tuple(powerset(OPERATIONS))


def request_bind(force_request: Request, initial_state: int = 0) -> frozenset[BoundTrace]:
    """Model Request(q,C,k) >>= (v,C') => Request(q,C,lambda r.k(r)>>=B)."""
    out = {
        BoundTrace(
            request=force_request,
            phase="pending-request",
            pending_suffix=("RebindResultPath", "B_f", "ReturnFromInvocation"),
            response=None,
            live_state=initial_state,
        )
    }
    for response, resumed_state in force_request.responses:
        out.add(
            BoundTrace(
                request=force_request,
                phase="resumed-suffix",
                pending_suffix=("RebindResultPath", "B_f", "ReturnFromInvocation"),
                response=response,
                live_state=resumed_state,
            )
        )
    return frozenset(out)


def required_outer_support(request: Request, handler_ops: frozenset[str]) -> frozenset[str]:
    """Full hygiene: no explicit capture contract means no caller-q subtraction."""
    # Inner handler ownership/operation coverage alone does not provide typed
    # callback capture incidence. The caller-owned request stays in outward c.
    _ = handler_ops
    return frozenset({request.operation})


def row_match_subtraction_mutant(
    request: Request, handler_ops: frozenset[str], f_argument_effect_component: str
) -> frozenset[str]:
    """Wrong shortcut: reuse of b plus matching handler head is treated as capture."""
    support = {request.operation}
    if f_argument_effect_component == SHARED_COMPONENT and request.operation in handler_ops:
        support.remove(request.operation)
    return frozenset(support)


VALUE_ENTRY_SUFFIX = ("RebindResultPath", "B_f", "ReturnFromInvocation")


def make_force_prefix(
    operations: tuple[str, ...], responses: tuple[tuple[int, int], ...]
) -> ForcePrefix:
    """Reconstruct the source prefix independently from its response history."""
    assert len(responses) <= len(operations)
    completed = tuple(
        Request(
            operation=operations[index],
            origin=f"request-origin:g-x:{index}",
            event_id=f"event:g-x:{index}",
            fiber=FIBER,
            typed_path=f"J_arg:g-to-f/{index}",
            responses=frozenset({response}),
        )
        for index, response in enumerate(responses)
    )
    next_index = len(responses)
    pending = None
    if next_index < len(operations):
        pending = Request(
            operation=operations[next_index],
            origin=f"request-origin:g-x:{next_index}",
            event_id=f"event:g-x:{next_index}",
            fiber=FIBER,
            typed_path=f"J_arg:g-to-f/{next_index}",
            responses=frozenset(),
        )
        suffix = tuple(
            f"Force(g):{index}" for index in range(next_index + 1, len(operations))
        ) + VALUE_ENTRY_SUFFIX
    else:
        suffix = VALUE_ENTRY_SUFFIX
    live_state = responses[-1][1] if responses else 0
    return ForcePrefix(completed, pending, live_state, suffix)


def resume_force_prefix(
    prefix: ForcePrefix,
    operations: tuple[str, ...],
    response: tuple[int, int],
) -> ForcePrefix:
    """Consume the pending event once, then expose the next source suffix."""
    assert prefix.pending_event is not None
    current = prefix.pending_event
    resumed_event = Request(
        operation=current.operation,
        origin=current.origin,
        event_id=current.event_id,
        fiber=current.fiber,
        typed_path=current.typed_path,
        responses=frozenset({response}),
    )
    completed = prefix.completed_events + (resumed_event,)
    next_index = len(completed)
    pending = None
    if next_index < len(operations):
        pending = Request(
            operation=operations[next_index],
            origin=f"request-origin:g-x:{next_index}",
            event_id=f"event:g-x:{next_index}",
            fiber=FIBER,
            typed_path=f"J_arg:g-to-f/{next_index}",
            responses=frozenset(),
        )
        suffix = tuple(
            f"Force(g):{index}" for index in range(next_index + 1, len(operations))
        ) + VALUE_ENTRY_SUFFIX
    else:
        suffix = VALUE_ENTRY_SUFFIX
    return ForcePrefix(completed, pending, response[1], suffix)


def replay_pending_mutant(
    prefix: ForcePrefix,
    operations: tuple[str, ...],
    response: tuple[int, int],
) -> ForcePrefix:
    """Deliberately replay the request before consuming its response."""
    correct = resume_force_prefix(prefix, operations, response)
    assert prefix.pending_event is not None
    return ForcePrefix(
        (prefix.pending_event,) + correct.completed_events,
        correct.pending_event,
        correct.live_state,
        correct.suffix,
    )


def minimal_mutant():
    request = Request(
        operation="Read",
        origin=ORIGIN,
        event_id=EVENT_ID,
        fiber=FIBER,
        typed_path=TYPED_PATH,
        responses=frozenset(),
    )
    handlers = frozenset({"Read"})
    exact = required_outer_support(request, handlers)
    mutant = row_match_subtraction_mutant(request, handlers, "b")
    assert exact == frozenset({"Read"}) and not mutant
    return request, handlers, exact, mutant


def minimal_replay_mutant():
    operations = ("Read",)
    pending = make_force_prefix(operations, ())
    response = (0, 0)
    correct = resume_force_prefix(pending, operations, response)
    mutant = replay_pending_mutant(pending, operations, response)
    assert correct != mutant
    assert len(correct.completed_events) == 1
    assert len(mutant.completed_events) == 2
    assert len({event.event_id for event in mutant.completed_events}) == 1
    return pending, response, correct, mutant


def exhaust() -> tuple[int, int]:
    cases = 0
    mutant_losses = 0
    for operation, responses, handler_ops in product(OPERATIONS, RESPONSES, HANDLER_SETS):
        request = Request(
            operation=operation,
            origin=ORIGIN,
            event_id=EVENT_ID,
            fiber=FIBER,
            typed_path=TYPED_PATH,
            responses=responses,
        )
        traces = request_bind(request)
        assert traces
        pending = {trace for trace in traces if trace.phase == "pending-request"}
        assert pending == {
            BoundTrace(
                request=request,
                phase="pending-request",
                pending_suffix=("RebindResultPath", "B_f", "ReturnFromInvocation"),
                response=None,
                live_state=0,
            )
        }
        resumed = {
            (trace.response, trace.live_state)
            for trace in traces
            if trace.phase == "resumed-suffix"
        }
        assert resumed == set(responses)
        assert all(trace.request == request for trace in traces)
        assert all(trace.pending_suffix == (
            "RebindResultPath", "B_f", "ReturnFromInvocation"
        ) for trace in traces)
        assert all(
            trace.request.fiber == FIBER
            and trace.request.origin == ORIGIN
            and trace.request.event_id == EVENT_ID
            and trace.request.typed_path == TYPED_PATH
            for trace in traces
        )

        exact = required_outer_support(request, handler_ops)
        mutant = row_match_subtraction_mutant(request, handler_ops, "b")
        assert request.operation in exact
        if request.operation in handler_ops:
            assert request.operation not in mutant
            mutant_losses += 1
        else:
            assert mutant == exact
        cases += 1

    assert cases == 2 * 16 * 4 == 128
    assert mutant_losses == 2 * 16 * 2 == 64
    return cases, mutant_losses


def exhaust_multi_request_sequences() -> tuple[int, int, int]:
    """Stress source support vs event multiplicity through two Force requests.

    Each ordered operation sequence is kept as distinct request events. A
    response prefix can stop at any event (suspension) or complete the entire
    argument computation before the ordinary Value-entry suffix begins.
    """
    histories = 0
    transitions = 0
    mutant_losses = 0
    sequences = [()]
    sequences.extend((op,) for op in OPERATIONS)
    sequences.extend(product(OPERATIONS, repeat=2))

    response_choices = tuple(product(VALUES, STATES))
    for operations in sequences:
        # Every prefix is a possible suspended boundary; the full prefix also
        # represents successful completion of the argument computation.
        for prefix_length in range(len(operations) + 1):
            prefix = operations[:prefix_length]
            for responses in product(response_choices, repeat=prefix_length):
                run = make_force_prefix(operations, responses)
                completed = run.completed_events
                pending = (run.pending_event,) if run.pending_event else ()
                trace = completed + pending
                assert tuple(event.operation for event in completed) == prefix
                assert len({event.event_id for event in trace}) == len(trace)
                assert all(event.fiber == FIBER for event in trace)
                assert all(event.typed_path.endswith(f"/{i}") for i, event in enumerate(trace))
                assert run.live_state == (responses[-1][1] if responses else 0)

                # The complete source sequence determines outward support even
                # when later events remain latent in the Force suffix.
                support = frozenset(operations)
                # Covariant support is a set: repeating Read creates two source
                # occurrences but one public support point.
                assert len(support) <= len(operations)
                if len(operations) == 2 and operations[0] == operations[1]:
                    assert len(support) == 1

                for handlers in HANDLER_SETS:
                    expected = support  # no explicit capture contract
                    mutant = frozenset(
                        operation
                        for operation in support
                        if not (
                            SHARED_COMPONENT == "b" and operation in handlers
                        )
                    )
                    assert expected <= frozenset(OPERATIONS)
                    if support & handlers:
                        assert mutant != expected
                        mutant_losses += 1
                    else:
                        assert mutant == expected
                    histories += 1

                if pending:
                    next_index = prefix_length + 1
                    expected_suffix = tuple(
                        f"Force(g):{index}"
                        for index in range(next_index, len(operations))
                    ) + VALUE_ENTRY_SUFFIX
                    assert run.suffix == expected_suffix
                    for response in response_choices:
                        resumed = resume_force_prefix(run, operations, response)
                        rebuilt = make_force_prefix(operations, responses + (response,))
                        assert resumed == rebuilt
                        # The suspended event becomes exactly one completed
                        # event; only a later operation may become pending.
                        assert resumed.completed_events[:len(completed)] == completed
                        assert resumed.completed_events[len(completed)].event_id == run.pending_event.event_id
                        assert len({event.event_id for event in resumed.completed_events}) == len(resumed.completed_events)
                        transitions += 1
                else:
                    assert run.suffix == VALUE_ENTRY_SUFFIX

    # There are 95 response-prefix histories and four handler assignments.
    assert histories == 95 * 4
    assert transitions == 88
    return histories, transitions, mutant_losses


def main() -> None:
    cases, losses = exhaust()
    histories, transitions, sequence_losses = exhaust_multi_request_sequences()
    request, handlers, exact, mutant = minimal_mutant()
    replay_prefix, replay_response, replay_correct, replay_mutant = minimal_replay_mutant()
    assert request.responses == frozenset()  # smallest pending-prefix witness
    print(f"Force/Value-entry finite cases checked: {cases}")
    print("stateful Request bind preserves event, fiber, origin, path and suffix: pass")
    print(f"same-component row-match mutant loses outward support in {losses} cases")
    print(
        f"ordered zero-to-two-request traces checked: {histories}; "
        f"resumption transitions checked: {transitions}"
    )
    print(
        f"same-component subtraction mutant loses support on repeated/ordered "
        f"traces in {sequence_losses} handler assignments"
    )
    print(
        "minimal witness: pending Read from g at J_arg, f handles Read, no capture "
        f"contract; exact outward c={sorted(exact)}, mutant={sorted(mutant)}"
    )
    print(
        "minimum replay-mutant failure: one pending Read, response="
        f"{replay_response}; correct completions={len(replay_correct.completed_events)}, "
        f"mutant completions={len(replay_mutant.completed_events)} with one repeated event ID"
    )
    print(
        "scope: one caller-owned request and one Value-entry suffix; no explicit "
        "capture case, multi-request operational semantics, or production endpoint"
    )


if __name__ == "__main__":
    main()
