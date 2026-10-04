#!/usr/bin/env python3
"""Execute the finite Function-entry witness against value-only shadows.

The same structural value ports (Unit argument, Unit result) can describe a
Value-entry function that forces its inert argument and a retained
Computation-entry function whose body ignores that argument. With no eligible
handler, a request in the argument is visible through the first invocation
and absent from the second. This is a proof-core obstruction to importing
pure structural Function comparison as the complete Function query.

Run: python3 tools/research_function_shadow_obstruction.py
"""

from __future__ import annotations

from dataclasses import dataclass


UNIT = "unit"
OP = "q"


@dataclass(frozen=True)
class Returned:
    value: str
    state: int


@dataclass(frozen=True)
class Requested:
    operation: str
    state: int
    response: str
    resumed_state: int
    continuation_result: Returned


Trace = Returned | Requested


@dataclass(frozen=True)
class Receiver:
    entry: str
    arg_shadow: str
    result_shadow: str
    body_result: str


VALUE_RECEIVER = Receiver("Value", UNIT, UNIT, UNIT)
COMPUTATION_RECEIVER = Receiver("Computation", UNIT, UNIT, UNIT)


def force_and_bind(argument: Trace, body_result: str) -> Trace:
    """Force the inert argument and bind its result to the function body."""
    if isinstance(argument, Returned):
        return Returned(body_result, argument.state)
    return Requested(
        argument.operation,
        argument.state,
        argument.response,
        argument.resumed_state,
        Returned(body_result, argument.resumed_state),
    )


def invoke(receiver: Receiver, whole_argument: Trace) -> Trace:
    if receiver.entry == "Value":
        return force_and_bind(whole_argument, receiver.body_result)
    if receiver.entry == "Computation":
        # The candidate computation retains this argument but its body ignores it.
        return Returned(receiver.body_result, 0)
    raise AssertionError(receiver.entry)


def full_observation(trace: Trace) -> tuple:
    if isinstance(trace, Returned):
        return ("return", trace.value, trace.state)
    return (
        "request",
        trace.operation,
        trace.state,
        trace.response,
        trace.resumed_state,
        full_observation(trace.continuation_result),
    )


def value_shadow(receiver: Receiver) -> tuple[str, str]:
    """The pure structural Function shadow drops the entry/provider path."""
    return receiver.arg_shadow, receiver.result_shadow


def minimum_witness() -> tuple[Trace, Trace, Trace]:
    # One request, one response, one resumed state, and constant Unit bodies.
    inert_argument = Requested(
        OP,
        state=0,
        response=UNIT,
        resumed_state=0,
        continuation_result=Returned(UNIT, 0),
    )
    via_value = invoke(VALUE_RECEIVER, inert_argument)
    via_computation = invoke(COMPUTATION_RECEIVER, inert_argument)
    assert isinstance(via_value, Requested)
    assert isinstance(via_computation, Returned)
    assert value_shadow(VALUE_RECEIVER) == value_shadow(COMPUTATION_RECEIVER)
    assert full_observation(via_value) != full_observation(via_computation)
    return inert_argument, via_value, via_computation


def check_irreducibility() -> None:
    # Removing the only request removes the observation difference.
    quiet_argument = Returned(UNIT, 0)
    assert full_observation(invoke(VALUE_RECEIVER, quiet_argument)) == full_observation(
        invoke(COMPUTATION_RECEIVER, quiet_argument)
    )
    # Keeping the request but forcing the Value receiver's entry path is exactly
    # the one distinction lost by the value-only structural projection.
    assert value_shadow(VALUE_RECEIVER) == value_shadow(COMPUTATION_RECEIVER)


def main() -> None:
    inert_argument, via_value, via_computation = minimum_witness()
    check_irreducibility()
    print(f"Value receiver shadow: {value_shadow(VALUE_RECEIVER)}")
    print(f"Computation receiver shadow: {value_shadow(COMPUTATION_RECEIVER)}")
    print(f"inert argument: {full_observation(inert_argument)}")
    print(f"Value-entry invocation: {full_observation(via_value)}")
    print(f"unused Computation-entry invocation: {full_observation(via_computation)}")
    print("value-only shadow equality with distinct complete observations: confirmed")
    print(
        "scope: proof-core counterexample to shadow-based comparison reuse; "
        "not a source program, A <: B derivation, or production endpoint query"
    )


if __name__ == "__main__":
    main()
