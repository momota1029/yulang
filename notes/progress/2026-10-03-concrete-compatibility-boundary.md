# Concrete compatibility boundary audit

Date: 2026-10-03
Branch: `research/simple-sub-intrusion`
Mode: M3 semantic/source-authority clarification
Review budget: one architect pre-write audit, one implementation-source explorer,
and two independent bounded reviewers (`compiler_referee`, `spec_auditor`)

## Decision recorded

The user's current decision allows transitivity for bound propagation among
type variables. A concrete type pair is checked by a local compatibility
judgment that can resolve cast/adaptation evidence. Compatibility successes
do not enter one transitive concrete subtype closure. The supplied optional
Record chain is accepted by Oracle although its direct string-to-int optional
Record comparison is rejected. These observations constrain the successor
design but do not yet specify field adaptation or optional-Record source
syntax.

`notes/design/2026-10-03-concrete-compatibility-boundary.md` records the
relation split, preserves the declared mathematical scope of the reviewed
structural theorems, and makes evidence-preserving compatibility normalization
the next research gate. It grants no implementation authority.

## Bounded repository evidence

- `yu-solver::TermView` and `InferenceSession::constrain_live` represent
  polarized Function comparisons and variable-bound replay, but no Record or
  adapter constructor.
- `yu-types` has no Record or adapter constructor in its closed type algebra.
- Successor HIR excludes cast declarations from the current resolved
  expression envelope. The parser and stable-core corpus contain cast syntax
  and an implicit value-cast example.
- Successor named-Record type syntax requires `name: Type`; optional Record
  pattern defaults are different syntax and semantics.
- The typed-boundary adapter theorem covers fixed-shape Function/Thunk
  realization. It does not decide concrete compatibility or optional Records.
- Frozen Oracle Record comparisons and registered nominal casts use distinct
  paths. `enqueue_record_fields` skips absent lower fields and otherwise
  derives matching-field comparisons; specialization separately checks
  missing required upper fields and matching children. By contrast,
  `NominalCastNeeded` for different nominal paths adds candidate cast
  constraints, then eligible source boundaries resolve exact path candidates
  as missing, unique or ambiguous. The optional-Record examples therefore do
  not establish that Oracle routes them through the nominal cast table.
- Specialization recreates materialized source-boundary pairs for expression
  consumption, function bodies and computed definition signatures. Its local
  type graph then propagates variable-to-variable edges, stores variable to
  concrete bounds, and validates concrete Record pairs separately. This is
  evidence that concrete validation is not inferred solely from whether an
  earlier propagation step emitted a child comparison; complete transport of
  every inference obligation remains unproved.
- The Evidence VM has a recursive Record adapter path, but generic Record
  `Coerce` can lower to an alias, and the directional runtime-equivalence
  shortcut can preserve the original Record including extra fields. The
  recursive adapter rebuilds target fields, except deferred source-Thunk to
  non-Thunk fields; it does not resolve registered nominal casts recursively.
  Explicit Record literals can materialize registered casts at child fields.
  The older mono runtime returns supported Record values unchanged. These
  paths do not constitute one existing runtime resolver.
- Nominal cast handling also differs by phase: type-graph constraint
  generation instantiates all exact-path candidates, emission takes the first
  exact-path rule, and `CastTable::resolve_value` separately classifies
  missing/unique/ambiguous declarations. This remains historical evidence,
  not a candidate selection policy for the successor.

This evidence supports a common successor compatibility boundary only as a
candidate local dispatch interface across checking and resolution. Record
shape derivations, selected nominal cast evidence and executable adapter plans
must remain distinguishable unless a preservation proof justifies stronger
unification. It neither rejects the user's direction nor establishes that the
Oracle paths already share a runtime adapter mechanism.

The reviewed §5 candidate now makes the Record check phase-explicit: a missing
optional target field is permitted, a missing required target field is rejected
at concrete validation, extra lower fields are ignored, and shared fields
generate child compatibility obligations. Frozen inference skips a child
comparison for optional-lower/required-upper, while concrete validation still
checks a present matching child's type; the skip alone is not accepted as a
final result. This reproduces the supplied optional-Record discriminator
without transitive closure. It does not yet prove how a successor preserves
such obligations across phases or realizes the result at runtime.

The new draft passed bounded independent semantic and conformance reviews with
no findings. A further compiler-referee delta audit verified the frozen
Record and nominal-cast routes described above. The §5 proposal had an
architect pre-write audit and fresh compiler-referee and spec-auditor reviews;
all reported no findings within scope. The compiler referee did not audit the
whole successor call graph, full predecessor proofs or backend adapter
realization; the spec auditor did not run Oracle or tests. No code or test
expectations changed. A focused regression audit of the added specialization,
runtime and cast-route evidence found one qualification: thunk-to-value Record
fields may be deferred instead of recursively adapted. The text was updated
and the primary cross-checked that branch in the frozen runtime source.
`git diff --check` passed. No tests, builds or measurements were run.
Measurement budget consumed: 0.

This runtime-route delta used one read-only implementation-source explorer and
one independent regression auditor. The auditor found that source-Thunk to
non-Thunk Record fields may be deferred by the Evidence VM; the design note
now states that exception. The primary independently checked the cited
deferment branch. Review was limited to these added source-path claims and did
not re-audit the prior relation theorem or candidate Record table.

## Next gate

Prove that a source comparison judgment can preserve the Record-local checking
evidence tree across unresolved variable bounds and concrete specialization,
including how the specialization boundary relates to each original inference
obligation. Then specify adapter plans for identity-preserving versus
projecting Records, absence, extras and optional-to-required fields. Explore a
shared local dispatcher that keeps Record derivations, cast candidate
resolution and emitted adapter evidence distinct; do not copy the frozen
first-match/all-candidates discrepancy as a policy. Only then prove guarded
query generation from variable-bound propagation and evidence-preserving
residual factorization. Source-wide context finiteness, unknown Record shapes,
effectful interfaces, lifecycle and implementation remain open.
