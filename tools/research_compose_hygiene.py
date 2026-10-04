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


def main() -> None:
    cases, losses = exhaust()
    request, handlers, exact, mutant = minimal_mutant()
    assert request.responses == frozenset()  # smallest pending-prefix witness
    print(f"Force/Value-entry finite cases checked: {cases}")
    print("stateful Request bind preserves event, fiber, origin, path and suffix: pass")
    print(f"same-component row-match mutant loses outward support in {losses} cases")
    print(
        "minimal witness: pending Read from g at J_arg, f handles Read, no capture "
        f"contract; exact outward c={sorted(exact)}, mutant={sorted(mutant)}"
    )
    print(
        "scope: one caller-owned request and one Value-entry suffix; no explicit "
        "capture case, multi-request operational semantics, or production endpoint"
    )


if __name__ == "__main__":
    main()
