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

## User-selected product priorities (2026-09-24)

The user's product priority is Oracle-compatible observable behavior on the
practical supported-input envelope, with a lightweight implementation and
successful path. Do not trade away ordinary-input semantics for an
implementation shortcut or a theoretical optimization.

The user also accepts a bounded support envelope: pathologically deep, large,
or resource-intensive inputs may be rejected rather than supported at
arbitrary scale. This is permission to choose a proportionate deterministic
limit, not a requirement to build exhaustive recovery for every malformed or
resource-exhausting case. When choosing that boundary:

- Preserve memory safety, solver invariants for accepted inputs, and atomic
  publication. Reject before a limit can turn into stack exhaustion, runaway
  work/allocation, or partially visible output.
- State the measured or structural dimension and the deterministic rejection
  point. Do not silently truncate, approximate, or return a changed result.
- Oracle divergence is acceptable only outside the explicitly documented
  practical envelope; treat mismatches within it as bugs.
- Prefer the smallest mechanism that protects ordinary use. Do not add broad
  machinery solely for fantastically large or impossible cases when an early
  bounded rejection preserves the required safety properties.

This priority guides tradeoffs but does not silently rewrite a narrower
Authoritative language/API contract. For each affected feature, the concrete
supported-input boundary and failure behavior must be recorded in a narrow
addendum. If that changes an existing Authoritative contract, the addendum
must pass independent review, receive explicit user approval, and record its
supersession before implementation, following the approval gate below. The
user's delegation is to choose a practical route under these priorities, not
to conceal its observable boundary or its performance cost.

## Natural compiler behavior and proof-obligation economy (2026-10-07)

Authority: the user's explicit decision to keep Yulang's compiler behavior
natural while avoiding proof work that exists only because of an unnecessarily
proof-hostile design.

Proof convenience is subordinate to approved ordinary compiler behavior. Do not
make otherwise supported programs require artificial annotations, introduce
user-visible distinctions with no language purpose, reject natural inference
paths, or add runtime/source restrictions merely because those choices shorten a
metatheoretic proof.

For design and cutover planning, keep three claim classes distinct:

1. **Compiler safety/correctness**: properties needed so accepted programs,
   generated constraints/evidence, solving, generalization, instantiation and
   publication are sound for the supported envelope.
2. **Natural inference behavior**: completeness or usability properties needed
   for the ordinary source programs and inference behavior the language is
   intended to support.
3. **Stronger semantic characterization**: all-model, all-view, open-world,
   converse-completeness, maximal principality, or similar research theorems
   that are valuable but are stronger than what ordinary compiler operation
   requires.

Class 3 is not automatically a production-cutover prerequisite. It becomes one
only when an Authoritative design, an accepted observable-behavior contract, or
a concrete safety/correctness dependency requires it. Conversely, calling a
claim "research" never permits dropping a class-1 or class-2 obligation.

Persistent proof obligations are design feedback. When a proof repeatedly has
to reconstruct ownership, provenance, incidence, licensing, scope, provider
identity, or another fact that the owning compiler phase already knew while
constructing the program representation, prefer retaining a canonical typed
certificate or explicit phase output over proving the fact later from IDs,
shapes, successful queries, or duplicated semantic relations. Such retained
evidence must be a natural byproduct of the approved compiler operation; it
must not invent new language meaning merely to make a theorem easy.

When two designs preserve the same approved observable behavior and safety
contract, prefer the one with a single authority for each fact, more
syntax-/construction-directed evidence, fewer inverse/reconstruction theorems,
and a smaller semantic surface that must be trusted simultaneously.

This policy does **not** close, retire, weaken, or reclassify any current proof
obligation by itself. Existing DAG gates keep their recorded status until a
reviewed argument shows that a gate is discharged or is unnecessary for the
selected production contract. Any actual semantic weakening or change to an
Authoritative contract still follows the normal approval and supersession gate.

## Active withdrawal of Simple-sub bypasses (2026-10-10)

The user's explicit [withdrawal decision](../notes/design/2026-10-10-simple-sub-legacy-withdrawal.md)
requires removal of legacy inference dependencies replaced by Simple-sub's
constraint generation, propagation, levels, extrusion, intrusion and
generalization. Adding a parallel successor path does not satisfy this decision.
For each replaced local decision rule, early satisfiability requirement,
source-shape special case or registry prerequisite, identify its actual owner
and consumers, remove the implementation dependency, and verify the replacement
with focused regressions where executable evidence is available.

Remove obsolete proof prerequisites from the active dependency graph with a
recorded replacement and reason. Do not leave them as unresolved current gates
or mark them proved. Preserve historical proof material with explicit historical
status; it cannot override the selected successor design. Complete Call meaning,
effect hygiene, soundness and principality remain genuine requirements. Their
missing proofs or compiler correspondence cannot be closed by retiring an old
construction route.

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
