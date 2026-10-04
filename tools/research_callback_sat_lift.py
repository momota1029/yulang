#!/usr/bin/env python3
"""Finite operational check of scalar Sat_j under the checked callback lift.

The probe composes finite Force(argument) computations with the local
integer-body abstraction from callback-local-abstraction-boundary.md. It checks
exact identity/literal bodies embed in Sat_j, and that checked construction
adds only total projections to each complete old tuple and pending request. A
finite lexical-scope identifier and typed-path labels are copied as tuple
fields; quantifier scope and joint hiding are not modeled. An equality mutant
demonstrates why the abstract output coordinate stays distinct from the
lexical argument coordinate.

This is characterization evidence for the bounded scalar contract only. It is
not a Function endpoint interpretation, callback adequacy theorem, or
production inference model.

Run: python3 tools/research_callback_sat_lift.py
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product


Fiber = tuple[str, str, str]  # fixed nu, K, D identifiers
INTS = (0, 1)
STATES = (0, 1)


@dataclass(frozen=True, order=True)
class Response:
    response: int
    live_state: int


@dataclass(frozen=True, order=True)
class Challenge:
    label: str
    initial_state: int
    # None means a direct Force return. Each request has its own response set.
    direct_value: int | None
    request_relations: tuple[tuple[Response, ...], ...] = ()


@dataclass(frozen=True, order=True)
class Observation:
    fiber: Fiber
    challenge: str
    binder_scope: str
    typed_paths: tuple[str, ...]
    phase: str
    initial_state: int
    forced_value: int | None
    body_value: int | None
    live_state: int
    response_history: tuple[tuple[int, int, int], ...]
    events: tuple[str, ...]
    pending_suffix: tuple[str, ...]
    body_occurrence: str
    source_identities: tuple[str, ...]


@dataclass(frozen=True, order=True)
class Lifted:
    old: Observation
    # Each added coordinate is a total function of the complete old tuple.
    d_projection: tuple[object, ...]
    b_projection: tuple[object, ...]


def relation_powerset():
    pairs = tuple(Response(response, state) for response, state in product(INTS, STATES))
    for size in range(len(pairs) + 1):
        yield from (tuple(xs) for xs in combinations(pairs, size))


RELATIONS = tuple(relation_powerset())


def challenge_graphs() -> tuple[Challenge, ...]:
    out: list[Challenge] = []
    for state, value in product(STATES, INTS):
        out.append(Challenge(f"return-s{state}-v{value}", state, value))
    for state in STATES:
        for rel in RELATIONS:
            out.append(
                Challenge(
                    f"request-s{state}-r{RELATIONS.index(rel)}",
                    state,
                    None,
                    (rel,),
                )
            )
        for first, second in product(RELATIONS, repeat=2):
            out.append(
                Challenge(
                    f"request2-s{state}-r{RELATIONS.index(first)}-{RELATIONS.index(second)}",
                    state,
                    None,
                    (first, second),
                )
            )
    assert len(out) == 2 * (2 + 16 + 16**2) == 548
    return tuple(out)


def source_identities(challenge: Challenge) -> tuple[str, ...]:
    return (
        "outer-apply-owner",
        "latent-invocation-owner",
        f"{challenge.label}:d-",
        f"{challenge.label}:d+",
        f"{challenge.label}:b+",
        "callback-receipt",
        "argument-receipt",
        *(f"{challenge.label}:request-{i}" for i in range(len(challenge.request_relations))),
    )


def binder_scope(challenge: Challenge) -> str:
    return f"{challenge.label}:lambda-scope"


def typed_paths(challenge: Challenge) -> tuple[str, ...]:
    return (f"{challenge.label}:J_arg", f"{challenge.label}:J_call")


def base_events() -> tuple[str, ...]:
    return (
        "callback-receipt",
        "argument-receipt",
        "invoke:Pure:Value",
        "force:whole-argument",
    )


def remaining_suffix(challenge: Challenge, next_request: int) -> tuple[str, ...]:
    return tuple(
        f"request:E_arg-{i}" for i in range(next_request, len(challenge.request_relations))
    ) + ("rebind", "Sat_j", "result-consumer", "return")


def force_paths(challenge: Challenge, fiber: Fiber) -> set[Observation]:
    """Enumerate pending prefixes and completed Force returns with live state."""
    identities = source_identities(challenge)
    body_occurrence = f"{challenge.label}:body"
    if challenge.direct_value is not None:
        return {
            Observation(
                fiber,
                challenge.label,
                binder_scope(challenge),
                typed_paths(challenge),
                "force-return",
                challenge.initial_state,
                challenge.direct_value,
                None,
                challenge.initial_state,
                (),
                base_events() + ("force-return",),
                (),
                body_occurrence,
                identities,
            )
        }

    observations: set[Observation] = set()

    def visit(
        request_index: int,
        live_state: int,
        history: tuple[tuple[int, int, int], ...],
        events: tuple[str, ...],
    ) -> None:
        request_event = f"request:E_arg-{request_index}"
        observations.add(
            Observation(
                fiber,
                challenge.label,
                binder_scope(challenge),
                typed_paths(challenge),
                "pending-request",
                challenge.initial_state,
                None,
                None,
                live_state,
                history,
                events + (request_event,),
                remaining_suffix(challenge, request_index + 1),
                body_occurrence,
                identities,
            )
        )
        for answer in challenge.request_relations[request_index]:
            next_history = history + ((request_index, answer.response, answer.live_state),)
            next_events = events + (
                request_event,
                f"resume:{request_index}:{answer.response}:state-{answer.live_state}",
            )
            if request_index + 1 == len(challenge.request_relations):
                observations.add(
                    Observation(
                        fiber,
                        challenge.label,
                        binder_scope(challenge),
                        typed_paths(challenge),
                        "force-return",
                        challenge.initial_state,
                        answer.response,
                        None,
                        answer.live_state,
                        next_history,
                        next_events + ("force-return",),
                        (),
                        body_occurrence,
                        identities,
                    )
                )
            else:
                visit(
                    request_index + 1,
                    answer.live_state,
                    next_history,
                    next_events,
                )

    visit(0, challenge.initial_state, (), base_events())
    return observations


def sat_observations(challenge: Challenge, fiber: Fiber) -> set[Observation]:
    """Apply Sat_j(a,v,C,C) after each Force return; retain pending prefixes."""
    out: set[Observation] = set()
    for forced in force_paths(challenge, fiber):
        if forced.phase == "pending-request":
            out.add(forced)
            continue
        for value in INTS:
            out.add(
                Observation(
                    forced.fiber,
                    forced.challenge,
                    forced.binder_scope,
                    forced.typed_paths,
                    "complete",
                    forced.initial_state,
                    forced.forced_value,
                    value,
                    forced.live_state,
                    forced.response_history,
                    forced.events + ("rebind", "result-consumer", "return"),
                    (),
                    forced.body_occurrence,
                    forced.source_identities,
                )
            )
    return out


def exact_body_observations(
    challenge: Challenge, fiber: Fiber, mode: str
) -> set[Observation]:
    """Exact identity or literal body, on the same finite Force paths."""
    out: set[Observation] = set()
    literal = 0
    for forced in force_paths(challenge, fiber):
        if forced.phase == "pending-request":
            out.add(forced)
            continue
        assert forced.forced_value is not None
        result = forced.forced_value if mode == "identity" else literal
        out.add(
            Observation(
                forced.fiber,
                forced.challenge,
                forced.binder_scope,
                forced.typed_paths,
                "complete",
                forced.initial_state,
                forced.forced_value,
                result,
                forced.live_state,
                forced.response_history,
                forced.events + ("rebind", "result-consumer", "return"),
                (),
                forced.body_occurrence,
                forced.source_identities,
            )
        )
    return out


def total_extension(old: Observation) -> Lifted:
    d = (old.challenge, old.forced_value, old.phase, old.response_history)
    b = (old.body_occurrence, old.body_value, old.phase, old.live_state)
    return Lifted(old, d, b)


def erase(rows: set[Lifted]) -> set[Observation]:
    return {row.old for row in rows}


def exact_identity_checked_mutant(challenge: Challenge, fiber: Fiber) -> set[Observation]:
    return {
        row
        for row in sat_observations(challenge, fiber)
        if row.phase != "complete" or row.body_value == row.forced_value
    }


def check() -> tuple[int, int, int, int, int, Observation, Observation]:
    fiber = ("nu-0", "K-0", "D-0")
    graphs = challenge_graphs()

    actual: set[Observation] = set()
    checked: set[Lifted] = set()
    exact_identity: set[Observation] = set()
    exact_literal: set[Observation] = set()
    for graph in graphs:
        abstract_rows = sat_observations(graph, fiber)
        actual |= abstract_rows
        exact_identity |= exact_body_observations(graph, fiber, "identity")
        exact_literal |= exact_body_observations(graph, fiber, "literal")
        lifted = {total_extension(row) for row in abstract_rows}
        assert erase(lifted) == abstract_rows
        assert all(row.old.fiber == fiber for row in lifted)
        assert all(row.old.binder_scope == binder_scope(graph) for row in lifted)
        assert all(row.old.typed_paths == typed_paths(graph) for row in lifted)
        assert all(row.old.source_identities == source_identities(graph) for row in lifted)
        assert all(
            row.d_projection
            == (row.old.challenge, row.old.forced_value, row.old.phase, row.old.response_history)
            and row.b_projection
            == (row.old.body_occurrence, row.old.body_value, row.old.phase, row.old.live_state)
            for row in lifted
        )
        assert all(
            row.old.live_state
            == (row.old.response_history[-1][2] if row.old.response_history else row.old.initial_state)
            for row in lifted
        )
        checked |= lifted

    checked_old = erase(checked)
    assert actual <= checked_old
    assert checked_old == actual
    assert exact_identity <= actual
    assert exact_literal <= actual

    mutant = set().union(
        *(exact_identity_checked_mutant(graph, fiber) for graph in graphs)
    )
    lost = actual - mutant
    assert lost
    absolute_minimum = min(
        (row for row in lost if row.phase == "complete" and not row.response_history),
        key=lambda row: (row.initial_state, row.forced_value, row.body_value, row.challenge),
    )
    assert absolute_minimum.forced_value != absolute_minimum.body_value
    # The concrete resumption witness from the scalar abstraction criterion:
    # one request resumes with value 1 in state 0, then Sat_j chooses 0.
    chosen = next(
        graph
        for graph in graphs
        if graph.initial_state == 0
        and graph.request_relations == ((Response(1, 0),),)
    )
    resumption_witness = next(
        row
        for row in sat_observations(chosen, fiber)
        if row.phase == "complete" and row.response_history == ((0, 1, 0),)
        and row.body_value == 0
    )
    assert resumption_witness.forced_value == 1 and resumption_witness.live_state == 0
    assert resumption_witness in sat_observations(chosen, fiber)
    assert resumption_witness not in exact_identity_checked_mutant(chosen, fiber)
    return (
        len(graphs),
        len(actual),
        len(exact_identity),
        len(exact_literal),
        len(lost),
        absolute_minimum,
        resumption_witness,
    )


def main() -> None:
    graph_count, abstract_count, identity_count, literal_count, lost_count, absolute, resumed = check()
    print(f"finite Force argument graphs: {graph_count}")
    print(f"pending and completed abstract observations: {abstract_count}")
    print(f"exact identity observations embedded in Sat_j: {identity_count}")
    print(f"exact integer-zero literal observations embedded in Sat_j: {literal_count}")
    print("checked total-coordinate lift: projection equals the complete old relation")
    print(f"observations lost by v=a checked mutant: {lost_count}")
    print(
        "lexicographically least direct-return loss under "
        "(initial state, input, result, challenge): "
        f"input={absolute.forced_value}, result={absolute.body_value}, state={absolute.live_state}"
    )
    print(
        "one-request resumption loss: "
        f"history={resumed.response_history}, input={resumed.forced_value}, "
        f"result={resumed.body_value}, state={resumed.live_state}"
    )
    print(
        "scope: scalar Sat_j, at most two request layers, and total-coordinate lift; "
        "no production endpoint denotation, higher-order values, or general handler"
    )


if __name__ == "__main__":
    main()
