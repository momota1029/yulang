# Negative annotation license: source construction obstruction

Date: 2026-10-12
Status: frozen bounded derivation; independently reviewed with one minor factual correction applied
Claim class: bounded source characterization and local consumer derivation
Original annotation-license premise, native residual equation and hygiene H: OPEN
Baseline: `79f5fc15bd652f8b86cea73721ffd452cb99c9d7`
Branch: `research/simple-sub-intrusion`
Producer: primary-assigned constructive proof leaf; no delegation
Exclusive lease: this file only

## 1. Frozen statement and authority

For every program in the original successfully lowered source domain of
[H](2026-10-11-oracle-global-effect-hygiene-proof.md) §1, every actual
composed-negative concrete annotation occurrence, its original lexical scope
and binders, and every actual copy and call/output route, derive from the
source construction which concrete lower contribution/fiber participates in
that occurrence's local subtraction. The derivation must identify the exact
set-wide attachment, resolved member ordinal and operand, and actual route;
an independent contribution at the same resolved effect on the same identified
row must survive. Distinct residual constructions retain distinct lineages.
Symbolic tails remain connected to their original binders and later checks.

This is the Y3 source bridge needed to use that original contract, not a claim
restricted to currently admitted candidate programs. Rejection of a negative
constructor does not discharge its source case. Successful source lowering
does not require accepting an incorrect typing: authentic checks/errors and
safe nonpublication are allowed. Actual provider, contribution, call/output
witness, demand tail and residual lineage cannot be selected independently.
For a reached demand `u <: Row(I,t) @ chi`, `t` is its actual tail; it is not
replaced with annotation binder `x`. The required association must be derived
before the residual owner uses it, not supplied as an `AttachmentLicense`,
eligibility relation, route map or separation hypothesis.

Authority: [top-level inference principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5; [annotation hygiene integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4; [attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–4, including §3.1; and [residual lineage selection](../design/2026-10-10-contextual-residual-lineage-selection.md),
“Selected policy” and “Preserved contract and open obligations”. One attachment
identity belongs to one exact occurrence's atom set; members retain ordinals.
Composed contravariance permits local subtraction; covariance permits effects.
The withdrawn callback scheme supplies no expected output.

Shared assumptions for the static conclusions are the pinned bytes and normal
completed owning calls with valid handles and allocation before exhaustion.
These assumptions supply no negative constructor, source-to-fiber association,
complete replay, soundness or principality. This leaf uses the reviewed
[native payload obstruction](2026-10-12-native-negative-residual-equation-proof.md)
and [source-owner route](../progress/2026-10-12-negative-recipe-owner-source-route.md)
without promoting their conditional premises. No new representation or semantic
rule is adopted. Compiler/tests/shared records, executable probes, Oracle runs,
Git mutation and source-admission enabling are excluded.

## 2. Actual construction identities

Source locators below refer to the baseline. Solver filenames are under
`crates/yu-solver/src/`; the HIR owner is under `crates/yu-hir/src/`.

| Owner | Actual output and its scope |
| --- | --- |
| `crates/yu-hir/src/module/source_annotation.rs:68–93,350–375,505–561` | `SourceAnnotation(owner,position,ty)`; each `SourceEffectRow(position,concrete,variables)` retains its exact syntax occurrence, resolved declaration IDs and symbolic names. `SourceEffectId` is module plus declaration identity, not spelling. The inspected parser supports nullary operands; this fact does not narrow the original claim. |
| `candidate_effect.rs:979–997` | `candidate_formal_effect_variable` maps `(AnnotationScope,name)` to the original live effect row. Scopes distinguish definition, local binding and expression (`:40`). This map provides a binder connection, not subtraction authority. |
| `candidate_effect.rs:1358–1445,1447–1577` | Function recursion reverses composed variance for arguments and preserves it for results. A per-construction `views[row.position]` shares a view between the paired endpoints for one row occurrence. The negative-concrete guard precedes tail lookup and view allocation (`:1507`). |
| `candidate_effect.rs:733–773`; `candidate_context.rs:2174–2197` | For an annotation view allocated with `attachment_source=Some(...)`, the fresh view ID and `LocalWeightId` identify a weight retaining owner, row position, boundary=view ID, members, composed polarity, lexical scope and ordinals `0..allowed.len()`. Generic annotation/check views can omit this attachment source and then retain only their owner, position, boundary and allowed members. The weight ID is the set identity when a weight exists. Live left/right words are empty. `SourceUnitPush` is positive-only dormant preparation, with a detached adapter (`:2200–2215`). |
| `candidate_effect.rs:888–917` | Processing `Support(v)` emits `AnnotationMember(v,m)` for each actual member, plus the actual tail constraint. Thus this endpoint retains an association to its originating view/member rather than just a nominal family. |
| `candidate_effect.rs:140–144,864–886` | `Contribution(i)` stores resolved effect, `SourceNodeKey` origin and instance ID. Its allocator takes effect and origin, not an attachment or route. This alone is not evidence that all source provenance was discarded. |
| `candidate_context.rs:205–211,267–271,2488–2532` | `RelationId` names `(TypedPairKey,ContextId)`; `Origin` associates it with an actual `ConstraintOccurrenceId` and optional inferred-entry handle. Source seeding derives a context from a closed Allowance only. Empty negative attachment bundles are linked to source constraints but are inert and contain no concrete members (`candidate_effect.rs:1280–1315`). |

**Construction lemma.** For two distinct completed `candidate_signature_view`
allocations in one surviving arena state, their view IDs differ; when both
allocate a source weight, their weight IDs also differ. Both IDs are allocated
from their respective vector lengths and then appended. This remains true if
owner, position, member vector or underlying row compares equal. A paired
construction can deliberately reuse one view through its local position map;
that does not merge two allocations. These are allocation facts, not a theorem
about all source occurrences, rollback epochs or all fresh-use semantics.

An important discriminator is already available: `AnnotationMember` can also
come from an **operation** view. `candidate_operation(:778–804)` retains an
`OperationOrigin` with declaration and occurrence; the root operation's result
port passes its actual family at `:1430–1443`. `candidate_signature_view` gives
operation views no source weight and records `ViewOrigin::Operation`. Therefore
the endpoint variant or effect identity alone cannot authenticate an annotation
grant. Conversely a view/member endpoint with annotation provenance preserves
useful source evidence; its mere existence does not grant subtraction.

## 3. Two direct derivation attempts

**Endpoint and view route.** Trace `SourceAnnotation` through
`candidate_source::execute_candidate_action(:660–688)` to the paired formal,
definition/ascription or local constructor. Negative concrete formation stops
at source preflight (`candidate_source.rs:117–132`), at the formal-pair guard
(`candidate_effect.rs:1034–1070`), or at the signature guard above. Local
construction additionally checks `preflight_local_annotation(:1131)`.
No inspected authentic negative concrete caller reaches the view allocator.
Negative symbolic rows return their scoped row directly; empty negative rows
return bottom/empty, with the separately retained inert empty bundle. They do
not constitute the required concrete case.

The low-level view helper accepts an `AttachmentSource`, but supplying negative
metadata to it is not a source derivation. An open view has
`closed_weight=None` even when its source weight retains an attachment.
`candidate_context_source(:2488–2495)` consequently creates identity context
for that open Allowance; `candidate_zero_word_filters(:2649–2656)` requires the
exact closed-weight/view association. No existing negative continuation or
fiber selection follows from the metadata alone.

**Consumer lemma, with its exact local scope.** Fix a reached call to
`candidate_check_effect_operand(:918–948)` with upper `Allowance(v)` and a
lower `Contribution(i)` or `AnnotationMember(w,m)`. Its acceptance decision
reads only the lower's resolved `SourceEffectId` and the upper's allowed set.
If membership succeeds it returns `Ok(())`; otherwise it forwards the same
lower endpoint to the actual tail, or reports mismatch for a closed view.
Consequently two distinct valid lower endpoints with equal resolved effects
receive the same membership/forwarding choice at this fixed upper, although
their forwarded endpoints and possible diagnostics retain distinct identities.
The code never consults the contribution origin/instance or the lower view's
attachment/provenance to choose subtraction. This follows by substitution in
the two effect-extraction arms and their common membership test. It is a local
consumer derivation, not a reached negative source example or a claim that
nominal allowance checking itself is wrong. It rules out extracting the desired
asymmetric subtraction from **that decision alone**.

**Joint origin and relation route.** `candidate_bound_origin_with_evidence`
(`candidate_effect.rs:420–470`) passes `(bound,origin,RelationId,cause)` together.
`BoundEvidence::admit` groups admissions by `(BoundKey,RelationId)`
(`candidate_context.rs:530–578`). This preserves joint records; it must not be
replaced with independent choices from origin and context lists.
However OwnerEmission explicitly marks missing processing antecedents, ordinary
seed authentication and antecedent evidence (`:534–538`). Fiber transport adds
`MissingOriginAssociation(:588–603)`; replay evidence records unretained use
antecedents (`:613–622`). These records have no authorization consumer.
An origin identifies a constraint occurrence; no inspected owner derives from
it that a particular same-family lower is attached to this negative annotation
on this actual route.

This is not just an inference from field absence. The executable closed-filter
owner (`candidate_context_execute_relation:2744–2812`) checks/registers each
weight on the actual lower via `candidate_apply_effect`; its checked-bound
test (`:2820–2856`) verifies the receiver, current relation and closed boundary.
It establishes an allowance-check derivation, not a negative subtraction
selection. The effect application owner (`candidate_extrusion.rs:840–863`)
inserts level-oriented bounds and replays, or calls the nominal consumer; it
does not form residual `J/kappa/beta/pi_t` or select an attached lower.
Ordered replay (`candidate_context_begin_replay:2911–2982`) keeps the actual
lower/upper fibers and their shared child contexts. It cannot create an
unemitted source grant merely by combining them.

## 4. Minimal obstruction and counterexample status

The minimal unproved source rule is:

> At the actual negative annotation construction and its reached Row-demand
> reduction, derive from the original source interface and actual propagation
> history why this lower fiber participates in this occurrence/member's local
> subtraction on this route; retain that association while deriving the
> correlated residual consequences. A same-row same-family lower introduced
> independently of that association must reach the surviving consequence.

This is a required construction/consumer rule, not a proposed field, assumed
license relation or conditional theorem. HIR knows the resolved annotation,
scope and row occurrence. The source annotation/Function entry and actual
call/propagation owners must establish the relation to lower contributions;
it is not justified that the parser already knows all later call routes. The
Row-demand owner must consume that same derivation. Source position equality,
row equality, nominal family membership and the `AnnotationMember` tag each
fail to supply it separately. No source identity must be erased to make this
problem visible: existing retained identities lack the establishing operation.

**No source-qualified pair falsifying H is established here.** The local
two-endpoint consumer lemma uses supplied valid endpoints and a reached
Allowance call. It does not authenticate two actual negative source derivations
meeting on one row and one demand. The guards preclude that route in the
inspected candidate constructors. Thus current source correspondence is
incomplete, but there is no demonstrated accepted negative execution that
removes an independent contribution. Inventing such a pair, calling rejection
a vacuous proof, or calling the allowance lemma a hygiene counterexample would
overstate the evidence. The previously withdrawn callback output is unusable
as a falsifier.

Copy infrastructure does retain useful structure: capture keeps the whole
operand endpoint and view tail (`candidate_scheme.rs:445–455`); fresh use maps
`AnnotationMember` through the same per-use view map and copies a Contribution's
effect/origin with a fresh instance (`:1039–1070`). Extrusion likewise preserves
the member ordinal while remapping the view/tail (`candidate_extrusion.rs:180–203,277–291`).
These are direct transport statements, not a proof of full transport, qualifying
intrusion or route licensing. `canonical_effect(lib.rs:11447–11454)` identifies
only effect rows, leaving operand IDs intact. Equal rows therefore neither
destroy these identities automatically nor establish their semantic license.

## 5. Economy audit, coverage and handoff

The endpoint/view route and the joint evidence route leave the same source
association unproved. Under `rules/compiler-engineering.md`, required local
subtraction and independent survival remain A/B. Inferring grants later from
families, equal rows or disconnected marginal identities would create D debt.
The owning construction must first establish the actual association; retaining
an unproved label is insufficient. Existing transport can carry evidence only
after that establishment. Another inverse map, finite subtraction lemma or
reclassification does not close the premise. Stop here rather than attempt a
third equivalent reconstruction.

One next action: the primary assigns the original negative annotation/Function
entry and reached Row-demand owners a construction-specific derivation of this
association, including an authenticated independent same-family survivor,
before authorizing a proof-dependent residual implementation. The primary owns
design adjudication and fresh independent review. No source restriction,
ordinary-inference weakening or promotion follows from this note.

Checks: bounded `cat`, `sed`, `rg`, read-only branch/HEAD/status; complete-file
baseline/hash comparison and artifact whitespace/link checks. Some initial
combined captures truncated; all decisive source excerpts and governing
sections used here were reread in bounded captures. The checkout has no `spec/`
directory; attempted specification lookup supplied no premise. No test/build,
Oracle/executable probe, measurements, Git mutation or shared-record write ran.
Initial independent read batches used up to five lightweight shell calls;
later reads were sequential. No heavy or persistent process and no child ran.
CPU/RAM and cumulative subprocess count were not instrumented. This leaf stays
within its allocated 35-minute wall budget; exact runtime model/effort metadata
is unavailable. Normal requested routing is Sol/high; inspected config defaults
are `gpt-6.1-sol/high`, and the prover role omits model/effort pins. No Astra or
hot reload is claimed.

Omitted/unverified: actual negative construction, authenticated same-row source
pair, complete Call/provider binding, residual payload equation and activation,
complete current/future replay, non-nullary operands, global effect hygiene,
all capture/extrusion/intrusion paths, generalization, normal progress,
soundness, required principality and cutover. Prior bounded algebra results
remain available with their original hypotheses. Writes stop at handoff.

## Commit packet

- Exact lease: `notes/theory/2026-10-12-negative-annotation-license-source-proof.md`.
- Baseline: `79f5fc15bd652f8b86cea73721ffd452cb99c9d7`.
- Changed dependency hashes: none at final comparison; frozen hashes below.
- Honest status: independently reviewed bounded source obstruction/local
  derivation; original parent gates remain OPEN; no source-qualified H
  counterexample.
- Checks already run: decisive owner reads/search, complete dependency hash
  comparison, leased-note relative links/whitespace/final newline; no execution.
- Proposed message: `research: locate negative annotation source license obstruction`.
- Shared-record deltas left to primary/curator: retain the OPEN association
  premise; distinguish annotation and operation member provenance; record
  nominal-only allowance choice and inert joint evidence without claiming
  identity loss; require authenticated same-row source separation before the
  residual construction gate. No shared record was edited.

### Independent review

A `compiler_referee` reviewed the bounded construction, endpoint provenance,
consumer lemma, route guards and stated theorem limits. It found no blocking or
major issue. One minor factual overstatement was corrected above: only
allocations with `attachment_source=Some(...)` retain the attachment metadata;
generic annotation/check views may omit it. The review does not close source
association, negative residual execution, independent-source survival or H.

### Frozen direct dependencies

All complete-file bytes matched the pinned baseline.

| Path | SHA-256 |
| --- | --- |
| `.codex/config.toml` | `dae388e4e811c346727ec6688472c7fcf6341ddc5466168cfaa03fdcc0b8e17a` |
| `.codex/agents/prover.toml` | `485a26c7409e16c692ad10095031ab0e7084726ec5da5666082b3bbc4a5daf98` |
| `rules/orchestration-budget.md` | `a0a114b589e8920af8e8fd871d15f63d68b735fc1a553f5a89952b1eab8489e5` |
| `rules/agent-orchestration.md` | `3b1e9c5a083ae4257d3d8ad4bacadf55adf07997d0b02c10bcbec4ccda3258be` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/theory/2026-10-12-native-negative-residual-equation-proof.md` | `b342082c43f5e0ebedb6736bc9b72ca722b0e7fa742e9575b579f7985be50779` |
| `notes/progress/2026-10-12-negative-recipe-owner-source-route.md` | `759fbdb78f405f3e8e963e37f264e8c31097c25cb9fc9b29bfb256b3eb718d16` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
