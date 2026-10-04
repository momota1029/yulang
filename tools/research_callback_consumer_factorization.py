#!/usr/bin/env python3
"""Differential finite model for Force/body/result-consumer composition.

The model compares two executable constructions over a tiny relational source
graph. The reference side uses `Force(D) >>= rebind >>= body >>= consumer`
with request continuations that retain their suffix. The independent side
walks the three source stages directly. It checks that request occurrences
from Force map to d-/d+ and body plus designated consumer map to b+, while
preserving values, state, owners, tuples, scopes, and the fixed nu/K/D fiber.

This is an exploratory source-composition model, not production endpoint
denotation or a callback adequacy/principality proof.

Run: python3 tools/research_callback_consumer_factorization.py
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import combinations, product


VALUES = (0, 1)
STATES = (0, 1)
FIBER = ("nu0", "K0", "D0")


@dataclass(frozen=True, order=True)
class Event:
    stage: str
    kind: str
    value: int | None
    state: int
    occurrence: str
    origin: str
    continuation: str


@dataclass(frozen=True, order=True)
class Observation:
    fiber: tuple[str, str, str]
    owner: str
    tuple_id: str
    latent_owner: str
    latent_tuple: str
    binder_scope: str
    typed_paths: tuple[str, str]
    phase: str
    value: int | None
    state: int
    events: tuple[Event, ...]
    pending_suffix: tuple[str, ...]
    d_minus: tuple[str, ...]
    d_plus: tuple[str, ...]
    b_plus: tuple[str, ...]


@dataclass(frozen=True)
class Done:
    value: int
    state: int
    events: tuple[Event, ...] = ()


@dataclass(frozen=True)
class Choice:
    options: tuple[Comp, ...]


@dataclass(frozen=True)
class Ask:
    event: Event
    responses: tuple[tuple[int, int, Comp], ...]
    prefix: tuple[Event, ...] = ()


Comp = Done | Choice | Ask


@dataclass(frozen=True)
class Stage:
    name: str
    relation: frozenset[tuple[int, int]]
    requests: bool


RELATIONS = tuple(
    frozenset(pairs)
    for size in range(5)
    for pairs in combinations(tuple(product(VALUES, repeat=2)), size)
)


def bind(comp: Comp, suffix) -> Comp:
    if isinstance(comp, Done):
        return suffix(comp.value, comp.state)
    if isinstance(comp, Choice):
        return Choice(tuple(bind(option, suffix) for option in comp.options))
    return Ask(
        comp.event,
        tuple((value, state, bind(next_comp, suffix)) for value, state, next_comp in comp.responses),
        comp.prefix,
    )


def occurrence(graph: str, stage: str) -> str:
    return f"{graph}:{stage}:request"


def request_event(graph: str, stage: str, input_value: int, state: int) -> Event:
    return Event(
        stage,
        "request",
        input_value,
        state,
        occurrence(graph, stage),
        f"{graph}:{stage}:origin",
        f"{graph}:{stage}:continuation",
    )


def source_receipts(graph: str, state: int) -> tuple[Event, Event]:
    return (
        Event("outer", "callback-receipt", None, state, f"{graph}:callback-receipt", "", ""),
        Event("latent", "argument-receipt", None, state, f"{graph}:argument-receipt", "", ""),
    )


def stage_computation(graph: str, stage: Stage, input_value: int, state: int) -> Comp:
    outputs = sorted(out for source, out in stage.relation if source == input_value)
    if not stage.requests:
        return Choice(tuple(Done(out, state) for out in outputs))
    event = request_event(graph, stage.name, input_value, state)
    responses = tuple(
        (
            out,
            next_state,
            Done(out, next_state),
        )
        for out in outputs
        for next_state in STATES
    )
    return Ask(event, responses)


def compose_source(graph: str, argument: Stage, body: Stage, consumer: Stage, initial: int, state: int) -> Comp:
    force = stage_computation(graph, argument, initial, state)
    return bind(
        force,
        lambda value, live: bind(
            stage_computation(graph, body, value, live),
            lambda body_value, body_state: stage_computation(
                graph, consumer, body_value, body_state
            ),
        ),
    )


def source_rows(comp: Comp, graph: str, owner: str, tuple_id: str, latent_owner: str, latent_tuple: str, scope: str, initial_state: int = 0):
    """Enumerate every pending prefix and completed derivation."""
    def add(trace, event):
        return trace + (event,)

    def make(phase, value, state, events, suffix):
        arg_occurrences = tuple(event.occurrence for event in events if event.stage == "argument" and event.kind == "request")
        body_occurrences = tuple(
            event.occurrence
            for event in events
            if event.stage in ("body", "consumer") and event.kind == "request"
        )
        # d- and d+ are distinct occurrence identities for the same Force
        # source occurrence; b+ includes the designated result consumer.
        return Observation(
            FIBER,
            owner,
            tuple_id,
            latent_owner,
            latent_tuple,
            scope,
            (f"{graph}:J_arg", f"{graph}:J_call"),
            phase,
            value,
            state,
            events,
            suffix,
            tuple(f"{item}:d-" for item in arg_occurrences),
            tuple(f"{item}:d+" for item in arg_occurrences),
            tuple(f"{item}:b+" for item in body_occurrences),
        )

    def walk(node: Comp, events: tuple[Event, ...], suffix: tuple[str, ...]):
        if isinstance(node, Done):
            yield make("complete", node.value, node.state, events + node.events, ())
        elif isinstance(node, Choice):
            for option in node.options:
                yield from walk(option, events, suffix)
        else:
            pending_events = events + node.prefix + (node.event,)
            remaining = suffix_after(node.event.stage)
            yield make("pending", None, node.event.state, pending_events, remaining)
            for response, resumed_state, continuation in node.responses:
                resume = Event(
                    node.event.stage,
                    "resume",
                    response,
                    resumed_state,
                    node.event.occurrence,
                    node.event.origin,
                    node.event.continuation,
                )
                yield from walk(continuation, events + node.prefix + (node.event, resume), suffix)

    yield from walk(comp, source_receipts(graph, initial_state), ("rebind", "body", "consumer", "return"))


def suffix_after(stage: str) -> tuple[str, ...]:
    return {
        "argument": ("rebind", "body", "consumer", "return"),
        "body": ("consumer", "return"),
        "consumer": ("return",),
    }[stage]


def direct_source_rows(graph: str, argument: Stage, body: Stage, consumer: Stage, initial: int, state: int, owner: str, tuple_id: str, latent_owner: str, latent_tuple: str, scope: str):
    """Independent explicit stage walker; it does not call `bind` or source_rows."""
    out: set[Observation] = set()

    def outputs(stage, value):
        return sorted(result for source, result in stage.relation if source == value)

    def emit(stage_name, value, live_state, events, pending=False):
        arg_occurrences = tuple(event.occurrence for event in events if event.stage == "argument" and event.kind == "request")
        body_occurrences = tuple(event.occurrence for event in events if event.stage in ("body", "consumer") and event.kind == "request")
        out.add(Observation(
            FIBER, owner, tuple_id, latent_owner, latent_tuple, scope,
            (f"{graph}:J_arg", f"{graph}:J_call"), "pending" if pending else "complete",
            None if pending else value, live_state, events,
            direct_remaining_stages(stage_name) if pending else (),
            tuple(f"{item}:d-" for item in arg_occurrences),
            tuple(f"{item}:d+" for item in arg_occurrences),
            tuple(f"{item}:b+" for item in body_occurrences),
        ))

    def stage(stage_spec, input_value, live_state, events, continuation):
        candidates = outputs(stage_spec, input_value)
        if stage_spec.requests:
            req = request_event(graph, stage_spec.name, input_value, live_state)
            prefix = events + (req,)
            emit(stage_spec.name, None, live_state, prefix, pending=True)
            for candidate in candidates:
                for next_state in STATES:
                    resume = Event(stage_spec.name, "resume", candidate, next_state, req.occurrence, req.origin, req.continuation)
                    continuation(candidate, next_state, prefix + (resume,))
        elif not stage_spec.requests:
            for candidate in candidates:
                continuation(candidate, live_state, events)

    stage(argument, initial, state, source_receipts(graph, state), lambda arg_value, arg_state, trace: stage(
        body, arg_value, arg_state, trace, lambda body_value, body_state, body_trace: stage(
            consumer, body_value, body_state, body_trace,
            lambda result, result_state, result_trace: emit("return", result, result_state, result_trace),
        ),
    ))
    return out


def direct_remaining_stages(stage_name: str) -> tuple[str, ...]:
    """Compute suffix from the direct walk's stage list, not the bind model."""
    stages = ("argument", "body", "consumer")
    next_stages = stages[stages.index(stage_name) + 1 :]
    before_body_rebind = ("rebind",) if stage_name == "argument" else ()
    return before_body_rebind + next_stages + ("return",)


def audit_projection(row: Observation) -> None:
    argument_occurrences = tuple(
        event.occurrence for event in row.events
        if event.stage == "argument" and event.kind == "request"
    )
    body_occurrences = tuple(
        event.occurrence for event in row.events
        if event.stage in ("body", "consumer") and event.kind == "request"
    )
    assert row.d_minus == tuple(f"{item}:d-" for item in argument_occurrences)
    assert row.d_plus == tuple(f"{item}:d+" for item in argument_occurrences)
    assert row.b_plus == tuple(f"{item}:b+" for item in body_occurrences)


def reject_minimized_mutants() -> tuple[int, int]:
    """The one-row cases detect omitted consumer incidence and Force replay."""
    owner, tuple_id = "outer:min", "tuple:min"
    latent_owner, latent_tuple, scope = "latent:min", "latent-tuple:min", "scope:min"

    # One direct Force result, one body result, and one consumer request with
    # one response is the smallest trace where consumer must contribute to b+.
    graph = "min-consumer"
    identity = frozenset({(0, 0)})
    stages = (
        Stage("argument", identity, False),
        Stage("body", identity, False),
        Stage("consumer", identity, True),
    )
    consumer_rows = set(source_rows(
        compose_source(graph, *stages, 0, 0), graph, owner, tuple_id,
        latent_owner, latent_tuple, scope,
    ))
    witness = next(row for row in consumer_rows if row.phase == "complete")
    assert witness.b_plus == ("min-consumer:consumer:request:b+",)
    omitted_consumer = replace(witness, b_plus=())
    try:
        audit_projection(omitted_consumer)
    except AssertionError:
        omitted_rejected = 1
    else:
        raise AssertionError("projection accepted omission of consumer contribution")

    # One argument request followed by one consumer request is the minimum
    # trace exposing a replay of an already completed Force after resumption.
    graph = "min-replay"
    stages = (
        Stage("argument", identity, True),
        Stage("body", identity, False),
        Stage("consumer", identity, True),
    )
    replay_rows = set(source_rows(
        compose_source(graph, *stages, 0, 0), graph, owner, tuple_id,
        latent_owner, latent_tuple, scope,
    ))
    completed = next(
        row for row in replay_rows
        if row.phase == "complete"
        and any(event.stage == "consumer" and event.kind == "resume" for event in row.events)
    )
    prior_force = next(event for event in completed.events if event.stage == "argument" and event.kind == "request")
    replayed = replace(
        completed,
        events=completed.events + (prior_force,),
        d_minus=completed.d_minus + (f"{prior_force.occurrence}:d-",),
        d_plus=completed.d_plus + (f"{prior_force.occurrence}:d+",),
    )
    try:
        audit_projection(replayed)
    except AssertionError:
        raise AssertionError("consistently projected replay should reach source-history comparison")
    expected_rows = direct_source_rows(
        graph, *stages, 0, 0, owner, tuple_id, latent_owner, latent_tuple, scope
    )
    assert replayed not in expected_rows
    replay_rejected = 1
    return omitted_rejected, replay_rejected


def run():
    checked_graphs = 0
    observations = 0
    consumer_bplus_rows = 0
    for request_flags in product((False, True), repeat=3):
        argument = Stage("argument", frozenset(product(VALUES, VALUES)), request_flags[0])
        for body_relation, consumer_relation, initial, state in product(RELATIONS, RELATIONS, VALUES, STATES):
            body = Stage("body", body_relation, request_flags[1])
            consumer = Stage("consumer", consumer_relation, request_flags[2])
            graph = f"g{checked_graphs}"
            owner, tuple_id, scope = f"outer:{graph}", f"tuple:{graph}", f"scope:{graph}"
            comp = compose_source(graph, argument, body, consumer, initial, state)
            latent_owner, latent_tuple = f"latent:{graph}", f"latent-tuple:{graph}"
            monadic = set(source_rows(comp, graph, owner, tuple_id, latent_owner, latent_tuple, scope, state))
            direct = direct_source_rows(graph, argument, body, consumer, initial, state, owner, tuple_id, latent_owner, latent_tuple, scope)
            assert monadic == direct, (request_flags, body_relation, consumer_relation, monadic ^ direct)
            assert all(
                row.fiber == FIBER and row.owner == owner and row.tuple_id == tuple_id
                and row.latent_owner == latent_owner and row.latent_tuple == latent_tuple
                and row.binder_scope == scope and row.typed_paths == (f"{graph}:J_arg", f"{graph}:J_call")
                for row in monadic
            )
            for row in monadic:
                assert tuple(event.kind for event in row.events if event.kind.endswith("receipt")) == (
                    "callback-receipt", "argument-receipt"
                )
                audit_projection(row)
                consumer_events = tuple(event.occurrence for event in row.events if event.stage == "consumer" and event.kind == "request")
                if consumer_events and row.phase == "complete":
                    assert {f"{item}:b+" for item in consumer_events} <= set(row.b_plus)
                    consumer_bplus_rows += 1
                observations += 1
            checked_graphs += 1
    assert checked_graphs == 8 * 16 * 16 * 2 * 2 == 8192
    assert consumer_bplus_rows > 0
    return checked_graphs, observations, consumer_bplus_rows


def main():
    graph_count, observation_count, consumer_rows = run()
    omitted_rejected, replay_rejected = reject_minimized_mutants()
    print(f"three-stage relation graphs checked: {graph_count}")
    print(f"pending-prefix and completed observations compared: {observation_count}")
    print(f"completed consumer-request observations retained in b+: {consumer_rows}")
    print("monadic bind/resumption and independent source-stage walk agree")
    print(f"minimized omitted-consumer b+ mutant rejected: {omitted_rejected}/1")
    print(f"minimized consistently projected Force-replay mutant rejected by source history: {replay_rejected}/1")
    print("scope: two values/states; 8 request shapes; two arbitrary binary relations; at most 3 requests")


if __name__ == "__main__":
    main()
