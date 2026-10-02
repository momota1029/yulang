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

## Boundary-conservation correction

A bounded architect audit found that the prior §2 candidate sentence deriving
`Compat(A,B)` whenever a variable path exposed concrete endpoints was not
justified by the user's authority. Under the conditional interpretation where
`Compat(A,X)` and `Compat(X,B)` remain separate suspended local obligations,
assigning `X={}` satisfies both optional-Record checks while direct
`Compat(A,B)` fails. Therefore variable-bound transitivity alone cannot
license an unconditional concrete lower/upper cross-product.

The candidate now retains source-boundary identities and requires source
semantics to justify any moved bound payload or additional concrete query.
The next theorem is boundary-obligation conservation under a shared
assignment: original guarded checks are neither lost nor replaced, and any
additional mandatory query must have its own source derivation. This does not
settle the source meaning of variable bounds or suspended checks. The
candidate edit received clean bounded compiler-referee and spec-auditor
reviews; both confirmed the conditional counterexample and unresolved source
semantics. No implementation or tests were run. This clarification preserves
the user's relation split and does not extend ordinary structural closure.

## Explicit bound-replay route

A follow-up frozen-source read found that Oracle has a specific same-variable
lower/upper replay rule. `cpk_lower_bound_replay_actions` prepares routes from a
new lower bound to existing uppers; `cpk_upper_bound_replay_actions` does the
symmetric operation. Eligible replay comparisons retain
`BinaryReplayDerivation { pivot, lower, upper, rule }` and replay claim parents;
trivial, duplicate and evidence-only routes can be prefiltered. An independent
architect audit confirmed the significance: this is a bound-derived concrete
query, not composition of two successful local compatibility judgments. The
conditional `X={}` counterexample only rejects interpreting the pair of local
checks as the entire variable-bound semantics; it does not refute a distinct
bound-replay judgment.

The theorem gate is therefore refined from plain boundary-obligation
conservation to bound-replay conservation: establish which source bound
premises admit replay, preserve original boundaries and replay parent
identities, prove no mandatory query is lost or unjustifiably added, and retain
the generated query's own local conversion evidence. The frozen proof parents
do not locate the runtime expression boundary for executing that conversion.
Architect pre-write audit plus independent compiler-referee and spec-auditor
reviews found no blocking or major semantic/conformance issue. Both reviewers
identified one factual overstatement that replay plans always enqueue; the text
now records route eligibility and prefiltering. No tests or builds were run.

The design now sketches the judgment split as candidate rules: variable edges
transport lower/upper bound payloads, while a same-pivot lower/upper pair
generates a fresh locally resolved `Compat` query. The compiler referee found
no semantic finding and confirmed that no successful `Compat` judgment is a
premise of those rules. The spec auditor found no conformance finding and
confirmed that source typing, guard propagation, principal solving and
conversion placement remain unapproved proof obligations. The equations are
not implementation authority.

The finite fixed-graph closure lemma is now recorded in
`notes/design/2026-10-03-finite-bound-replay-closure.md`. Independent semantic
and conformance review found two minor formal gaps: context domains and replay
key counting, and the fixed background facts needed by conditional model
conservation. The primary repaired both and clarified that unresolved
endpoints stay suspended because this lemma defines no solving rule. Review
confirmed the approved distinction: no successful concrete `Compat` judgment
is composed. The lemma proves only finite least closure and conditional
conservation for the abstract rules; source meaning, guard soundness,
boundary-replay completeness, conversion placement and source-wide finiteness
remain open. No implementation, tests, builds or measurements were run.
Measurement budget consumed: 0.

The next semantic audit asked whether replay follows from treating lower and
upper payloads as independent suspended checks. It does not: with optional
Record endpoints `{foo?: string}`, `{}`, `{foo?: int}`, the two local checks
pass while replay's direct check fails. This is recorded as a necessary
condition, not a rejection of the frozen replay route. A transparent
producer/consumer port is one conditional hypothesis: variable transport keeps
the producer view intact, while an actual concrete adaptation boundary ends
that transport and starts a new producer contract. Fresh compiler-referee and
spec-auditor reviews found no issue in the hypothesis' presentation; neither
establishes source applicability. Frozen-source inspection then grounded a
producer-to-local-to-consumer path through open value slots and located
registered casts at concrete function-argument consumption/emission. A local
annotation constrains the same existing value slot and does not establish a
conversion boundary. The design draft now cites the frozen local-lowering,
specialization and argument-emission owners; a bounded semantic delta review
found no issue. A follow-up clarification now says a successful check alone
does not by itself establish a new consumer-facing contract. The contract
could be sealed by a source check even if runtime preserves the original value;
conversion evidence and typed-view evidence are separate. A reviewer found a
major overclaim in the prior version, which incorrectly made emitted conversion
necessary. The primary revised the hypothesis to leave check-only typed views
open for source proof; the same reviewer confirmed the major finding is closed
with no new issue. Successor source generation and exact Record adapter
placement remain unverified.
No tests, builds or measurements were run.
Measurement budget consumed: 0.

## Next gate

Prove bound-replay conservation for a fixed finite source elaboration and
closed Record shapes. Define concrete-to-variable bound meaning and admissible
same-pivot replay; prove original guarded obligations and required replay
queries are preserved with their identities, without deriving queries from
successful `Compat` compositions. Prove finite replay provenance/context
closure before extending residual normalization. Then establish where replay
conversion evidence executes, specify Record adapter behavior and prove
evidence-preserving normalization and residual factorization. Source-wide
context finiteness, unknown Record shapes, effectful interfaces, lifecycle and
implementation remain open.
