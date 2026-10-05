#!/usr/bin/env python3
"""Join existing callback source and B-endpoint evidence models.

This bounded research check connects already-produced Force/body/consumer
observations to the existing callback endpoint trace audit. It does not define
production Function membership, a new evidence carrier, or an inequality rule.

Run: python3 tools/research_callback_endpoint_source_join.py
"""

from __future__ import annotations

from dataclasses import replace

import research_callback_consumer_factorization as source_model
import research_callback_endpoint_trace as endpoint_model


def observation_cases():
    graph = "joined"
    identity = frozenset(((0, 0), (1, 1)))
    argument = source_model.Stage("argument", identity, True)
    body = source_model.Stage("body", identity, True)
    consumer = source_model.Stage("consumer", identity, False)
    args = (
        graph,
        argument,
        body,
        consumer,
        0,
        0,
        "apply-owner",
        "apply-tuple",
        "latent-owner",
        "latent-tuple",
        "binder-scope",
    )
    reference = set(source_model.source_rows(
        source_model.compose_source(graph, argument, body, consumer, 0, 0),
        graph,
        "apply-owner",
        "apply-tuple",
        "latent-owner",
        "latent-tuple",
        "binder-scope",
    ))
    direct = source_model.direct_source_rows(*args)
    assert reference == direct

    # Keep one pending Body request (so d-/d+ and b+ all exist) and every
    # completed path. The silent result consumer contributes no request.
    selected = {
        row for row in reference
        if row.phase == "complete"
        or (
            row.phase == "pending"
            and any(event.stage == "body" and event.kind == "request" for event in row.events)
        )
    }
    assert selected
    assert all(row.fiber == source_model.FIBER for row in selected)
    return tuple(sorted(selected, key=repr))


def endpoint_source(row: source_model.Observation) -> endpoint_model.Source:
    """Project existing source occurrence coordinates into existing records."""
    source_model.audit_projection(row)
    argument_events = tuple(
        event for event in row.events
        if event.stage == "argument" and event.kind == "request"
    )
    body_events = tuple(
        event for event in row.events
        if event.stage == "body" and event.kind == "request"
    )
    if not argument_events or not body_events or not row.d_minus or not row.d_plus or not row.b_plus:
        raise ValueError("source observation lacks required d-/d+/b+ incidence")
    assert len(row.d_minus) == len(argument_events)
    assert len(row.d_plus) == len(argument_events)
    assert len(row.b_plus) == len(body_events)
    assert len(argument_events) == len(body_events) == 1
    assert row.d_minus == tuple(f"{event.occurrence}:d-" for event in argument_events)
    assert row.d_plus == tuple(f"{event.occurrence}:d+" for event in argument_events)
    assert row.b_plus == tuple(f"{event.occurrence}:b+" for event in body_events)

    def project(occurrence: str, component: str, path: str, attachment=None):
        return endpoint_model.Evidence(
            owner=row.latent_owner,
            scope=row.binder_scope,
            operand_tuple=row.latent_tuple,
            occurrence=occurrence,
            component=component,
            typed_path=path,
            attachment=attachment,
        )

    d_minus = project(row.d_minus[0], "argument", "Force")
    d_plus = project(row.d_plus[0], "argument", "CallView")
    b_plus = project(row.b_plus[0], "body", "CallView")
    assert d_minus.occurrence != d_plus.occurrence
    assert row.d_minus[0].rsplit(":", 1)[0] == row.d_plus[0].rsplit(":", 1)[0]
    assert row.typed_paths[0].endswith(":J_arg")
    assert row.typed_paths[1].endswith(":J_call")

    # The source owner/scope/tuple and independently generated endpoints are
    # fixed by this supplied callback-literal skeleton, not inferred from <:.
    return endpoint_model.Source(
        root="root0",
        apply_owner=row.owner,
        apply_tuple=row.tuple_id,
        lambda_label="lambda0",
        latent_owner=row.latent_owner,
        latent_tuple=row.latent_tuple,
        binder_scope=row.binder_scope,
        callback_boundary="F_cb0",
        parameter="P0",
        body="Body0",
        result="Result0",
        d_minus=d_minus,
        d_plus=d_plus,
        b_plus=b_plus,
        witnessed_attachments=frozenset(),
    )


def preserve_source_projection(row: source_model.Observation, source: endpoint_model.Source) -> None:
    assert source.apply_owner == row.owner
    assert source.apply_tuple == row.tuple_id
    assert source.latent_owner == row.latent_owner
    assert source.latent_tuple == row.latent_tuple
    assert source.binder_scope == row.binder_scope
    assert source.d_minus.occurrence == row.d_minus[0]
    assert source.d_plus.occurrence == row.d_plus[0]
    assert source.b_plus.occurrence == row.b_plus[0]
    assert source.d_minus.owner == source.d_plus.owner == source.b_plus.owner == row.latent_owner
    assert source.d_minus.operand_tuple == source.d_plus.operand_tuple == source.b_plus.operand_tuple == row.latent_tuple
    assert source.d_minus.scope == source.d_plus.scope == source.b_plus.scope == row.binder_scope
    # These source coordinates remain present in the input relation; the
    # endpoint trace does not claim to reify their runtime values or state.
    assert row.fiber == source_model.FIBER
    assert row.typed_paths == ("joined:J_arg", "joined:J_call")
    assert row.pending_suffix == ("consumer", "return") if row.phase == "pending" else not row.pending_suffix


def expect_rejected(thunk, label: str) -> None:
    try:
        thunk()
    except (AssertionError, ValueError):
        return
    raise AssertionError(f"audit accepted {label} mutant")


def main() -> None:
    rows = observation_cases()
    completed = 0
    pending = 0
    for row in rows:
        source = endpoint_source(row)
        trace = endpoint_model.generate(source)
        endpoint_model.audit(source, trace)
        preserve_source_projection(row, source)
        if row.phase == "complete":
            completed += 1
        else:
            pending += 1

    witness = next(row for row in rows if row.phase == "complete")
    source = endpoint_source(witness)
    trace = endpoint_model.generate(source)
    endpoint_model.audit(source, trace)

    expect_rejected(
        lambda: endpoint_model.audit(
            source,
            replace(trace, evidence=(source.d_minus, source.d_minus, source.b_plus)),
        ),
        "collapsed d-/d+ occurrence",
    )
    expect_rejected(
        lambda: endpoint_model.audit(
            source,
            replace(trace, latent_owner=trace.apply_owner),
        ),
        "owner substitution",
    )
    expect_rejected(
        lambda: endpoint_model.audit(
            source,
            replace(trace, binder_scope="other-scope"),
        ),
        "scope substitution",
    )
    missing_body = replace(
        witness,
        events=tuple(event for event in witness.events if event.stage != "body"),
        b_plus=(),
    )
    expect_rejected(lambda: endpoint_source(missing_body), "missing body incidence")
    substituted = replace(
        witness,
        d_minus=("ghost:d-",),
        d_plus=("ghost:d+",),
        b_plus=("ghost:b+",),
    )
    expect_rejected(lambda: endpoint_source(substituted), "substituted source incidence")

    print(f"source observations joined to existing B endpoint trace: {len(rows)}")
    print(f"pending Body request rows: {pending}; completed histories: {completed}")
    print("silent designated consumer retained in every source derivation")
    print("d-/d+ share one Force source event but retain distinct occurrence identities")
    print("b+ is projected only from an observed body request")
    print("occurrence-collapse, owner/scope substitution, missing/substituted-incidence mutants rejected: 5/5")
    print("scope: one finite operational-to-endpoint evidence bridge; no production membership, real Rel_C semantics, subtraction, containment, or principality")


if __name__ == "__main__":
    main()
