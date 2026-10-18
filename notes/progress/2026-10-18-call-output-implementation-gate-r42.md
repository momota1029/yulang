# R42 implementation prerequisite gate for Call output formation

Status: **read-only implementation gate**. This is not a patch plan with
current code authority. No source law is adopted, and `NO_SAFE_CODE_SLICE`
continues for unknown-author dirty Rust inputs.

Governing contract:
`tasks/agent-loop/sprints/call-output-owner-decision-20261018-r42.md`,
SHA-256 `c0b690dff2750713946a89324f2bb369c099aea39d4d29a62ebbc591437ad104`.
Reviewed input: R41 owner map
`notes/progress/2026-10-18-call-output-formation-owner-map-r41.md`, SHA-256
`0558299c19e83b9b9428843139e54fdcbca8b3bfd93427e2b322186d538bf0d9`.

## Authority gates before an implementation lease

The implementation path stays closed until the following order is complete:

1. The original Application/Call source owner supplies the exact
   `R41-UNIFORM-OUTPUT-HEADER` (or an authoritative replacement) with q's
   authentic declaration/reference, owner/class, source sort, scope and
   ordered typed dependency telescope. It must include the formal output/effect
   header law, actual primitive/root substitutions, complete `Q_q` arms and
   binder-before-use evidence. A native row, supplier request or endpoint
   solution cannot stand in for this rule.
2. The candidate receives independent design review, unresolved alternatives
   and explicit user approval before any new source semantic decision reaches
   implementation. Approval alone does not prove source preservation or
   close a parent theorem.
3. Source preservation/lifting, active Generalize consumer behavior and
   complete source/native result commutation get their own proofs and reviews.
   The original A/B scope, accepted source domain, both independent frames,
   aliases, arbitrary W, F1/FK1 and expected-output contract remain fixed.
4. The unknown-author dirty source owners become available under exact
   sequential leases and byte hashes for a narrowly defined source/generation
   change. Until then no writer overlap or edits are safe.

## Required certificate and path if authority is granted

The source schema must decide the fields; this list records the minimum
implementation questions and does not preselect their meaning:

| Certificate fact | Producer/retention gate | Consumer/copy gate |
| --- | --- | --- |
| Exact source event q, callee and argument origins, original Call reference | `ConstraintBatch::emit_candidate_source` must attach the authenticated source reference at Apply construction; existing recipe, occurrence and checking cause are retained | Admission and later observation must reject a certificate for t, h1/h2/h3, a different Apply, or a different original Q reference |
| Ordinary output-description origin, owner, class/sort, original scope, ordered `Delta_A` and typed context inclusion | The owning source formation rule must produce a typed descriptor certificate. Do not overload `introduction: Option<DirectionalIntroduction>` unless the approved design assigns it that exact type; currently `introduction:None` only describes the directional route | Check owner/scope/inclusion at formation; reject missing, inaccessible, reordered or post-use dependencies without inferring them from a native level or solved row |
| Value result, effect and full Call tuple | Keep Apply Value result distinct from application/callee/invocation effects. Retain actual returned provider/world, receiver role/entry, return and provider-dependent future references, continuation/receipt positions and every original arm interface | Consumer must distinguish `NativeInterface.result` from `.demand`, effects and actual provider. A Value Result comparison alone cannot certify the full Call tuple |
| Typed Result relation and provenance | Existing path is Apply source input → native admission → typed `FunctionField::Result` child → `Preserve`/`Dependency::FunctionPort` → Context/Dispatch | Revalidate source scope and complete tuple at the actual consumer; carry occurrence/source provenance and dependency through copies |
| Extrusion and copy lineage | Attach source certificate to each retained copy using the owning copy map and its actual context inclusion; never assert raw endpoint identity across rewrite | Reject a copy whose source context, dependency vector, occurrence lineage or owner mapping does not match the approved source certificate |
| Generalize/publication action | After a proof supplies source introduction and actual copy contexts, classify/fix/retain from original record classes and source scope | Check both independent incoming frames, aliases, all active consumers, F1 and FK1; no scheme eligibility or publication inferred from one local Call result |

The current R40 trace already maps native structural ownership at
`candidate_source.rs:1319–1360`, `shadow_apply.rs:1763–1895`,
`lib.rs:12655–12705,12807–12828,12354–12436`,
`candidate_context.rs:3375–3440`, and extrusion/copy handling at
`lib.rs:12588–12622`, `candidate_context.rs:3351–3372`, `lib.rs:13052–13070`.
This gate does not re-audit those bytes. It records the **additional source
certificate** and end-to-end proof that would be required if a reviewed and
approved design reaches implementation.

## Narrow future checks and falsifiers

Only after source law, design approval, exact ownership and proof obligations
are satisfied should a future implementation contract consider focused tests
for: wrong source occurrence; result/effect/provider substitution; missing or
reordered source dependency; changed `Q_q`/arm reference; loss or replay of
pending continuation/receipt; extrusion copy with mismatched source inclusion;
and Generalize under each original frame. Such tests would check a scoped
implementation; they would not prove source preservation or parent closure.

Exact falsifiers of an implementation certificate are a changed q/Q origin,
a result/effect or result/provider conflation, an unavailable dependency,
arm omission, altered event/continuation order, copy aliasing that changes a
source context, or a Generalize consumer action inconsistent with the approved
source formation judgment. No such implementation or test was attempted here.

## Scope, sources and receipt

Current read-only owners: `candidate_source.rs` and
`candidate_call.rs` emit/retain source Apply fields; `shadow_apply.rs` forms
the native demand/result; `lib.rs` builds and drives the typed Result child;
`candidate_context.rs` preserves the FunctionPort dependency. All are the
R41 contract's pinned, unknown-author dirty inputs. The current source contract
remains R41's missing uniform output header, not a native field.

Parent remains **OPEN, 0 → 0**. No expected output, semantic rule, test,
fixture or production source changed. Checks were static reading of R41 and
the pinned owner paths; no tests, Cargo, build, CLI, runtime or Git mutation.
This Luna gate uses its full 420-second grant; actual active duration, CPU and
RSS were not measured. Only this note and its assigned handoff were written;
no descendants or scratch outputs. The lane is frozen after the handoff hash.
