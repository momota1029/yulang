#!/usr/bin/env python3
"""Finite operational probe for the selected Value-entry callback path.

The model implements the ordinary-computation equations for Return/Request
bind and the selected `receipt; Force(D) >>= (v => RebindResultPath; B(v))`
source order. It exhausts small argument/body traces, including requests in
both places and sequential resumption across multiple requests. A mutation that forces the argument
before invocation is retained as a minimized counterexample.

This checks source operational ordering only. It does not interpret Function
ports, prove endpoint denotation/adequacy, implement Handler adaptation, or
model arbitrary owners/State/imports.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product


Event = str


@dataclass(frozen=True)
class Returned:
    value: int
    state: int
    events: tuple[Event, ...] = ()


@dataclass(frozen=True)
class Requested:
    operation: str
    state: int
    # Finite response relation for this small model.
    continuations: tuple[tuple[int, int, Trace], ...]
    events: tuple[Event, ...] = ()


Trace = Returned | Requested


@dataclass(frozen=True)
class CallableValue:
    introduction_role: str
    parameter_entry: str


@dataclass(frozen=True)
class CallbackSlotView:
    static_slot: str
    profile: str


def prepend(trace: Trace, events: tuple[Event, ...]) -> Trace:
    if isinstance(trace, Returned):
        return Returned(trace.value, trace.state, events + trace.events)
    return Requested(
        trace.operation,
        trace.state,
        trace.continuations,
        events + trace.events,
    )


def bind(trace: Trace, suffix) -> Trace:
    """State-threaded source bind, retaining a request's pending suffix."""
    if isinstance(trace, Returned):
        return prepend(suffix(trace.value, trace.state), trace.events)
    return Requested(
        trace.operation,
        trace.state,
        tuple(
            (response, resumed_state, bind(continuation, suffix))
            for response, resumed_state, continuation in trace.continuations
        ),
        trace.events,
    )


def resume(trace: Requested, response: int, resumed_state: int) -> Trace:
    for expected_response, expected_state, continuation in trace.continuations:
        if (expected_response, expected_state) == (response, resumed_state):
            return prepend(continuation, trace.events)
    raise KeyError((response, resumed_state))


def enumerate_completions(trace: Trace, request_budget: int = 3):
    if isinstance(trace, Returned):
        yield trace
        return
    if request_budget == 0:
        return
    for response, resumed_state, _ in trace.continuations:
        yield from enumerate_completions(
            resume(trace, response, resumed_state), request_budget - 1
        )


def request(
    operation: str,
    state: int,
    result_values: tuple[int, ...] = (0, 1),
) -> Requested:
    return Requested(
        operation,
        state,
        tuple(
            (response, (state + 1) % 2, Returned(response, (state + 1) % 2))
            for response in result_values
        ),
        (f"request:{operation}",),
    )


def callback_value_entry(
    value: CallableValue,
    slot: CallbackSlotView,
    argument_code: Trace,
    body,
) -> Trace:
    """Invoke the existing callable through a typed slot view, retaining role."""
    assert value.introduction_role == "Pure"
    assert value.parameter_entry == "Value"

    def after_force(argument_value: int, current_state: int) -> Trace:
        body_trace = body(argument_value, current_state)
        return prepend(body_trace, (f"rebind:{slot.static_slot}",))

    complete_invocation = bind(argument_code, after_force)
    return prepend(
        complete_invocation,
        (
            f"argument-reified:{slot.static_slot}",
            f"slot-view:{slot.static_slot}:{slot.profile}",
            f"call-receipt:{slot.static_slot}",
            "argument-receipt:whole-argument",
            f"invoke:{value.introduction_role}:{value.parameter_entry}",
            "force:whole-argument",
        ),
    )


def eager_argument_mutant(argument_code: Trace, body) -> Trace:
    """Mutant: force the represented argument before receiving it in the call."""
    def after_force(value: int, state: int) -> Trace:
        return prepend(body(value, state), ("call-receipt",))

    forced_before_call = prepend(argument_code, ("force:whole-argument",))
    return bind(forced_before_call, after_force)


def body_factory(mode: str):
    def body(value: int, state: int) -> Trace:
        if mode == "return":
            return Returned(value, state, (f"body:{value}:state-{state}",))
        if mode == "request":
            return prepend(
                request("E_body", state),
                (f"body:{value}:state-{state}",),
            )
        raise ValueError(mode)

    return body


def checked_invariants() -> tuple[int, int]:
    source = CallableValue("Pure", "Value")
    slot = CallbackSlotView("callback-0", "profile-0")
    scenarios = 0
    completed_paths = 0
    for argument_mode, body_mode in product(("return", "request"), repeat=2):
        for initial_state in (0, 1):
            if argument_mode == "return":
                argument = Returned(1, initial_state, ("argument-value-ready",))
            else:
                argument = request("E_arg", initial_state)
            observed = callback_value_entry(
                source,
                slot,
                argument,
                body_factory(body_mode),
            )
            assert source == CallableValue("Pure", "Value")

            for done in enumerate_completions(observed):
                events = done.events
                assert events.count("call-receipt:callback-0") == 1
                assert events.count("argument-receipt:whole-argument") == 1
                assert events.count("force:whole-argument") == 1
                assert events.count("slot-view:callback-0:profile-0") == 1
                assert events.count("invoke:Pure:Value") == 1
                assert events.count("rebind:callback-0") == 1
                assert sum(event.startswith("body:") for event in events) == 1
                assert done.state == ((initial_state + int(argument_mode == "request") + int(body_mode == "request")) % 2)

                receipt = events.index("call-receipt:callback-0")
                argument_receipt = events.index("argument-receipt:whole-argument")
                force = events.index("force:whole-argument")
                assert receipt < argument_receipt < force
                if argument_mode == "request":
                    request_index = events.index("request:E_arg")
                    assert force < request_index
                if body_mode == "request":
                    body_request = events.index("request:E_body")
                    assert events.index("rebind:callback-0") < body_request
                completed_paths += 1
            scenarios += 1
    return scenarios, completed_paths


def minimized_eager_counterexample() -> tuple[tuple[Event, ...], tuple[Event, ...]]:
    argument = request("E_arg", 0, result_values=(0,))
    source = CallableValue("Pure", "Value")
    slot = CallbackSlotView("callback-0", "profile-0")
    correct = callback_value_entry(source, slot, argument, body_factory("return"))
    mutant = eager_argument_mutant(argument, body_factory("return"))
    correct_done = next(enumerate_completions(correct, request_budget=1))
    mutant_done = next(enumerate_completions(mutant, request_budget=1))
    assert correct_done.events.index("call-receipt:callback-0") < correct_done.events.index("request:E_arg")
    assert correct_done.events.index("force:whole-argument") < correct_done.events.index("request:E_arg")
    assert mutant_done.events.index("force:whole-argument") < mutant_done.events.index("request:E_arg")
    assert mutant_done.events.index("request:E_arg") < mutant_done.events.index("call-receipt")
    return correct_done.events, mutant_done.events


def main() -> None:
    scenarios, completed_paths = checked_invariants()
    correct, mutant = minimized_eager_counterexample()
    print(f"Value-entry argument/body mode pairs and initial states: {scenarios}")
    print(f"finite response/resumption completions checked: {completed_paths}")
    print(f"minimal source-order path: {' -> '.join(correct)}")
    print(f"eager-force mutant path: {' -> '.join(mutant)}")
    print("scope: source-order and finite bind/resumption only; no endpoint-denotation theorem")


if __name__ == "__main__":
    main()
