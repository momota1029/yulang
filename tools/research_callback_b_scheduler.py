#!/usr/bin/env python3
"""Exercise role-first B callback generation on a finite source grammar.

This model covers only an Apply whose argument is one inline unary Lambda and
whose known callee exposes one callback boundary. It checks the reference
schedule in production-callback-endpoint-generation-draft.md §§2–3: reserve
the outer Apply, deliver expected callback context, select Handler before
visiting the body, synthesize the literal's endpoints independently, assemble
the completed Function endpoint from supplied source evidence, then emit one
ordinary inequality with that endpoint on the left.

No endpoint comparison algorithm or production evidence extraction is modeled.

Run: python3 tools/research_callback_b_scheduler.py
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import product


@dataclass(frozen=True)
class Name:
    spelling: str


@dataclass(frozen=True)
class Integer:
    value: int


@dataclass(frozen=True)
class Lambda:
    label: str
    parameter: str
    body: Name | Integer


@dataclass(frozen=True)
class Apply:
    label: str
    callee: str
    argument: Lambda
    callback_boundary: str


@dataclass(frozen=True)
class PortEvidence:
    argument_component: str
    d_minus_occurrence: str
    d_plus_occurrence: str
    body_component: str
    b_plus_occurrence: str
    latent_owner: str
    latent_tuple: str
    binder_scope: str
    d_minus_path: str = "J_arg/Force"
    d_plus_path: str = "J_call/CallView"
    b_plus_path: str = "J_call/CallView"


@dataclass(frozen=True)
class Generated:
    apply_owner: str
    apply_tuple: str
    latent_owner: str
    latent_tuple: str
    binder_scope: str
    role: str
    parameter_endpoint: str
    body_value_endpoint: str
    body_effect_endpoint: str
    result_endpoint: str
    completed_function: tuple[object, ...]
    query: tuple[str, tuple[object, ...], str]
    query_count: int
    order: tuple[str, ...]
    evidence: PortEvidence


def generate(app: Apply, evidence: PortEvidence) -> Generated:
    order = ["reserve-outer-apply"]
    expected = app.callback_boundary
    order.append("deliver-expected-callback-boundary")
    role = "Handler"  # selected before any Lambda body visit
    order.append("select-handler-role")

    parameter = f"{app.argument.label}:parameter"
    body_value = f"{app.argument.label}:body-value"
    body_effect = f"{app.argument.label}:body-effect"
    order.append("synthesize-parameter")
    order.append("synthesize-body")
    order.append("synthesize-result")

    d_minus = (
        evidence.argument_component,
        evidence.d_minus_occurrence,
        evidence.d_minus_path,
        evidence.latent_owner,
        evidence.latent_tuple,
        evidence.binder_scope,
    )
    d_plus = (
        evidence.argument_component,
        evidence.d_plus_occurrence,
        evidence.d_plus_path,
        evidence.latent_owner,
        evidence.latent_tuple,
        evidence.binder_scope,
    )
    b_plus = (
        evidence.body_component,
        evidence.b_plus_occurrence,
        evidence.b_plus_path,
        evidence.latent_owner,
        evidence.latent_tuple,
        evidence.binder_scope,
    )
    contravariant = (d_minus,)
    covariant = tuple(sorted((b_plus, d_plus)))
    completed = ("Fun", parameter, contravariant, covariant, body_value)
    order.append("assemble-completed-function")
    query = ("<:", completed, expected)
    order.append("emit-ordinary-inequality")
    return Generated(
        apply_owner=f"apply:{app.label}",
        apply_tuple=f"tuple:{app.label}",
        latent_owner=evidence.latent_owner,
        latent_tuple=evidence.latent_tuple,
        binder_scope=evidence.binder_scope,
        role=role,
        parameter_endpoint=parameter,
        body_value_endpoint=body_value,
        body_effect_endpoint=body_effect,
        result_endpoint=body_value,
        completed_function=completed,
        query=query,
        query_count=1,
        order=tuple(order),
        evidence=evidence,
    )


def audit(app: Apply, evidence: PortEvidence, generated: Generated) -> None:
    expected_prefix = (
        "reserve-outer-apply",
        "deliver-expected-callback-boundary",
        "select-handler-role",
    )
    assert generated.order[:3] == expected_prefix
    assert generated.order.index("select-handler-role") < generated.order.index("synthesize-body")
    assert generated.order.index("assemble-completed-function") < generated.order.index("emit-ordinary-inequality")
    assert generated.role == "Handler"
    assert generated.apply_owner != generated.latent_owner
    assert generated.apply_tuple != generated.latent_tuple
    assert generated.binder_scope == evidence.binder_scope
    assert evidence.latent_owner == generated.latent_owner
    assert evidence.latent_tuple == generated.latent_tuple
    assert evidence.d_minus_path == "J_arg/Force"
    assert evidence.d_plus_path == evidence.b_plus_path == "J_call/CallView"
    assert evidence.d_minus_occurrence != evidence.d_plus_occurrence
    assert evidence.body_component == generated.body_effect_endpoint
    assert evidence.latent_owner == generated.latent_owner
    assert evidence.latent_tuple == generated.latent_tuple
    assert evidence.binder_scope == generated.binder_scope
    assert generated.evidence == evidence
    assert generated.parameter_endpoint != app.callback_boundary
    assert generated.body_value_endpoint != app.callback_boundary
    assert generated.body_effect_endpoint != app.callback_boundary
    assert generated.completed_function[1] == generated.parameter_endpoint
    expected_d_minus = (
        evidence.argument_component,
        evidence.d_minus_occurrence,
        evidence.d_minus_path,
        evidence.latent_owner,
        evidence.latent_tuple,
        evidence.binder_scope,
    )
    expected_d_plus = (
        evidence.argument_component,
        evidence.d_plus_occurrence,
        evidence.d_plus_path,
        evidence.latent_owner,
        evidence.latent_tuple,
        evidence.binder_scope,
    )
    expected_b_plus = (
        evidence.body_component,
        evidence.b_plus_occurrence,
        evidence.b_plus_path,
        evidence.latent_owner,
        evidence.latent_tuple,
        evidence.binder_scope,
    )
    assert generated.completed_function[2] == (expected_d_minus,)
    assert generated.completed_function[3] == tuple(sorted((expected_b_plus, expected_d_plus)))
    assert generated.completed_function[-1] == generated.result_endpoint
    assert generated.query == ("<:", generated.completed_function, app.callback_boundary)
    assert generated.query_count == 1


def cases():
    count = 0
    for boundary, body in product(("Fcb0", "Fcb1"), (Name("x"), Integer(0))):
        app = Apply(
            label=f"site{count}",
            callee="host",
            argument=Lambda(f"lambda{count}", "x", body),
            callback_boundary=boundary,
        )
        evidence = PortEvidence(
            argument_component=f"arg-component{count}",
            d_minus_occurrence=f"d-minus{count}",
            d_plus_occurrence=f"d-plus{count}",
            body_component=f"lambda{count}:body-effect",
            b_plus_occurrence=f"b-plus{count}",
            latent_owner=f"latent-owner{count}",
            latent_tuple=f"latent-tuple{count}",
            binder_scope=f"scope{count}",
        )
        yield app, evidence
        count += 1
    assert count == 4


def main() -> None:
    generated_count = 0
    for app, evidence in cases():
        generated = generate(app, evidence)
        audit(app, evidence, generated)
        generated_count += 1
    assert generated_count == 4
    # A post-body context-delivery mutant is the minimum ordering violation.
    first_app, first_evidence = next(iter(cases()))
    valid = generate(first_app, first_evidence)
    trace = list(valid.order)
    role_index = trace.index("select-handler-role")
    body_index = trace.index("synthesize-body")
    trace[role_index], trace[body_index] = trace[body_index], trace[role_index]
    mutant = replace(valid, order=tuple(trace))
    try:
        audit(first_app, first_evidence, mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError("audit accepted role selection after body synthesis")
    dropped_ports = ("Fun", valid.parameter_endpoint, (), (), valid.result_endpoint)
    dropped_port_mutant = replace(
        valid,
        completed_function=dropped_ports,
        query=("<:", dropped_ports, first_app.callback_boundary),
    )
    try:
        audit(first_app, first_evidence, dropped_port_mutant)
    except AssertionError:
        pass
    else:
        raise AssertionError("audit accepted a completed Function with dropped effect ports")
    print(f"finite Apply + inline-Lambda cases checked: {generated_count}")
    print("callback boundary precedes Handler selection; Handler precedes body: pass")
    print("independent literal endpoints, latent/outer ownership, completed endpoint, and final B query: pass")
    print("post-body role-selection and dropped-effect-port mutants: rejected")
    print("scope: generation scheduling and endpoint wiring; evidence validity, endpoint semantics, and host invocation behavior excluded")


if __name__ == "__main__":
    main()
