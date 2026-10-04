#!/usr/bin/env python3
"""Bounded executable audit of callback B endpoint-generation traces.

This models only the finite constructor/evidence bookkeeping in
production-callback-endpoint-generation-draft.md §§2–4. It deliberately has no
endpoint denotation or inequality semantics: the source evidence is input,
and the checker verifies that generation preserves its owners, scopes,
occurrences, attachments, and independent endpoint synthesis before emitting
one final ordinary comparison.

Run: python3 tools/research_callback_endpoint_trace.py
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from itertools import product


@dataclass(frozen=True)
class Evidence:
    owner: str
    scope: str
    operand_tuple: str
    occurrence: str
    component: str
    typed_path: str
    attachment: str | None = None


@dataclass(frozen=True)
class Source:
    root: str
    apply_owner: str
    apply_tuple: str
    lambda_label: str
    latent_owner: str
    latent_tuple: str
    binder_scope: str
    callback_boundary: str
    # These are independently generated, opaque finite endpoint terms.
    parameter: str
    body: str
    result: str
    d_minus: Evidence
    d_plus: Evidence
    b_plus: Evidence
    witnessed_attachments: frozenset[str]


@dataclass(frozen=True)
class Trace:
    root: str
    apply_owner: str
    apply_tuple: str
    lambda_label: str
    latent_owner: str
    latent_tuple: str
    binder_scope: str
    role: str
    parameter: str
    body: str
    result: str
    contravariant_descriptor: tuple[str, str | None]
    covariant_row: tuple[str, ...]
    completed_function: tuple[object, ...]
    query: tuple[str, tuple[object, ...], str]
    query_count: int
    evidence: tuple[Evidence, ...]


def endpoint(e: Evidence) -> str:
    return f"{e.component}@{e.owner}/{e.typed_path}"


def generate(s: Source) -> Trace:
    # A concrete attachment is subtracted only when the source tuple carries
    # the corresponding existing subtraction evidence.
    attachment = s.d_minus.attachment
    retained = attachment if attachment not in s.witnessed_attachments else None
    dminus_view = endpoint(s.d_minus)
    dplus_view = endpoint(s.d_plus)
    bplus_view = endpoint(s.b_plus)
    contra = (dminus_view, retained)
    output = tuple(sorted((bplus_view, dplus_view)))
    completed_function = ("Fun", s.parameter, contra, output, s.result)
    return Trace(
        root=s.root,
        apply_owner=s.apply_owner,
        apply_tuple=s.apply_tuple,
        lambda_label=s.lambda_label,
        latent_owner=s.latent_owner,
        latent_tuple=s.latent_tuple,
        binder_scope=s.binder_scope,
        role="Handler",
        parameter=s.parameter,
        body=s.body,
        result=s.result,
        contravariant_descriptor=contra,
        covariant_row=output,
        completed_function=completed_function,
        query=("<:", completed_function, s.callback_boundary),
        query_count=1,
        evidence=(s.d_minus, s.d_plus, s.b_plus),
    )


def audit(s: Source, t: Trace) -> None:
    assert t.root == s.root
    assert t.apply_owner == s.apply_owner and t.apply_tuple == s.apply_tuple
    assert t.lambda_label == s.lambda_label
    assert t.latent_owner == s.latent_owner and t.latent_tuple == s.latent_tuple
    assert t.binder_scope == s.binder_scope
    assert t.apply_owner != t.latent_owner and t.apply_tuple != t.latent_tuple
    assert t.role == "Handler"
    assert (t.parameter, t.body, t.result) == (s.parameter, s.body, s.result)
    rows = (s.d_minus, s.d_plus, s.b_plus)
    assert all(e.owner == s.latent_owner for e in rows)
    assert all(e.operand_tuple == s.latent_tuple for e in rows)
    assert all(e.scope == s.binder_scope for e in rows)
    assert s.d_minus.typed_path == "Force"
    assert s.d_plus.typed_path == "CallView"
    assert s.b_plus.typed_path == "CallView"
    assert len({e.occurrence for e in rows}) == 3
    assert s.d_minus.component == s.d_plus.component
    assert s.d_minus.occurrence != s.d_plus.occurrence
    assert t.evidence == rows
    assert t.contravariant_descriptor[0] == endpoint(s.d_minus)
    expected_attachment = s.d_minus.attachment
    if expected_attachment in s.witnessed_attachments:
        expected_attachment = None
    assert t.contravariant_descriptor[1] == expected_attachment
    assert t.covariant_row == tuple(sorted((endpoint(s.b_plus), endpoint(s.d_plus))))
    expected_function = (
        "Fun", s.parameter, t.contravariant_descriptor, t.covariant_row, s.result
    )
    assert t.completed_function == expected_function
    assert t.query == ("<:", expected_function, s.callback_boundary)
    assert t.query_count == 1


def source_cases():
    # Exhaust the smallest owner/scope/evidence identity space, including
    # present/absent concrete attachment witnesses and independently chosen
    # parameter/body/result endpoint labels.
    cases = 0
    for apply_owner, latent_owner in (("A0", "L0"), ("A1", "L0")):
        for apply_tuple, latent_tuple in (("X0", "Y0"), ("X1", "Y0")):
            for scope in ("S0", "S1"):
                for parameter, body, result in product(("p0", "p1"), repeat=3):
                    for attachment, witnessed in product((None, "write"), (False, True)):
                        if attachment is None and witnessed:
                            continue
                        root = "R"
                        latent = "latent:" + latent_tuple
                        evidence = (
                            Evidence(latent, scope, latent_tuple, "d-0", "arg", "Force", attachment),
                            Evidence(latent, scope, latent_tuple, "d+-0", "arg", "CallView"),
                            Evidence(latent, scope, latent_tuple, "b+-0", "body", "CallView"),
                        )
                        yield Source(
                            root, apply_owner, apply_tuple, "lam0", latent,
                            latent_tuple, scope, "Fcb", parameter, body, result,
                            *evidence,
                            frozenset({attachment} if witnessed and attachment else ()),
                        )
                        cases += 1
    assert cases == 2 * 2 * 2 * 8 * 3


def minimal_mutant(source: Source, field: str) -> Trace:
    good = generate(source)
    if field == "owner":
        return replace(good, latent_owner=good.apply_owner)
    if field == "tuple":
        return replace(good, latent_tuple=good.apply_tuple)
    if field == "role":
        return replace(good, role="Pure")
    if field == "endpoint":
        return replace(good, parameter=source.callback_boundary)
    if field == "occurrence":
        return replace(good, evidence=(source.d_minus, source.d_minus, source.b_plus))
    if field == "attachment":
        return replace(good, contravariant_descriptor=(good.contravariant_descriptor[0], "write"))
    if field == "row":
        return replace(good, covariant_row=(endpoint(source.d_plus), endpoint(source.d_plus)))
    if field == "query":
        return replace(good, query_count=2)
    raise ValueError(field)


def main() -> None:
    sources = tuple(source_cases())
    for source in sources:
        trace = generate(source)
        audit(source, trace)
    mutants = ("owner", "tuple", "role", "endpoint", "occurrence", "attachment", "row", "query", "path")
    # Each mutant is checked against the lexicographically first minimal
    # source; rejection demonstrates the relevant audit obligation is active.
    witness = sources[0]
    rejected = 0
    for field in mutants:
        try:
            if field == "path":
                bad_dminus = replace(witness.d_minus, typed_path="CallView")
                bad_source = replace(witness, d_minus=bad_dminus)
                audit(bad_source, generate(bad_source))
            else:
                audit(witness, minimal_mutant(witness, field))
        except AssertionError:
            rejected += 1
        else:
            raise AssertionError(f"audit failed to reject {field} mutant")
    assert rejected == len(mutants)
    print(f"finite callback source traces audited: {len(sources)}")
    print("unique independently selected parameter/body/result endpoint triples: 8")
    print(f"deliberate trace mutants rejected: {rejected}/{len(mutants)}")
    print("owners, tuples, scopes, Handler role, selected d-/d+/b+ paths and incidence, witnessed attachment, completed Function operand, flat output row, and single final query: pass")
    print("scope: finite B-step constructor/evidence conformance only; no production endpoint denotation, bound inclusion, or principal-scheme claim")


if __name__ == "__main__":
    main()
