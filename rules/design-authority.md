# Design authority

## Authority order

When two instructions govern the same scope and conflict, use this order:

1. the user's current explicit decision;
2. an `Authoritative` design or specification whose declared scope covers the decision;
3. active repository rules under `rules/` and root hard invariants;
4. invariants expressed by current code and test contracts whose intent has been confirmed;
5. general engineering practice or model intuition.

Authority is scope-sensitive. A broad architecture document does not decide an unrelated local detail. A later narrow addendum overrides a broader document only where it explicitly says what it supersedes.

Implementation convenience never overrides an authoritative decision. When code and design appear inconsistent, stop the affected write, identify the exact conflict, and return it to the primary agent for adjudication or a user decision.

## Design status

New design documents use:

```text
Draft → Reviewed → Authoritative → Superseded
```

- `Draft`: under development; implementation is not bound by it.
- `Reviewed`: independently reviewed but not yet user-approved.
- `Authoritative`: the user approved the declared scope and decisions.
- `Superseded`: authority moved to a later document; keep the old document for history.

Recommended header:

```text
Status: Authoritative
Scope: <authority scope>
Approved-by: user
Approved-at: YYYY-MM-DD
Drafted-by: <role or source>
Reviewed-by: <independent roles>
Supersedes: <document or none>
```

`Drafted-by` and `Reviewed-by` record provenance, not authority. Model identity, model availability, authorship signature, and prose quality do not make a design authoritative.

## Approval and implementation gate

A design that makes a new language, API, semantic, architecture, performance, or durable workflow decision must not reach implementation until:

1. its scope and decision are explicit;
2. independent review has tested invariants, omissions, and rollback conditions;
3. unresolved alternatives are presented to the user;
4. user approval is recorded.

A confirmed design may define phases or gates. Implement the next confirmed gate instead of reopening the design. Re-enter design only when the implementation exposes a genuine contradiction, missing decision, false premise, or scope expansion.

## Legacy compatibility

Existing design documents are not rewritten merely to modernize model names.

- An existing document that explicitly says `ユーザ承認済み` is grandfathered as `Authoritative` within its stated scope.
- Signatures such as `著者: Claude (Fable 5)`, `Codex gpt-5.6-sol が起案`, or `Claude Sonnet 5 が査読` remain historical provenance.
- Loss or replacement of the named model does not weaken an approved decision.
- Old model-routing labels, including Fable/Sonnet substitute procedures or Sol/Terra/Luna selection prose, do not control current role routing.
- When changing an existing authoritative decision, create an addendum or successor with a new status header and explicit `Supersedes`; do not silently rewrite the old decision.

The authoritative navigation entry point is `notes/design/INDEX.md`. The index is a locator, not a substitute for the source document. If an index entry conflicts with the source, the source wins.

## Test contracts

A test expectation may encode an approved language or compiler contract. Do not change an expectation solely because the current implementation produces something else. Before changing expected output, determine whether the failure is an implementation defect or an approved specification change. See `rules/testing.md`.
