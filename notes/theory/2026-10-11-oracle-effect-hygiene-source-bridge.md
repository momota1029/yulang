# Oracle effect hygiene: an actual formal port and its missing subtraction bridge

Date: 2026-10-11
Status: frozen, independently reviewed bounded research derivation; no theorem or gate status promotion
Reviewed-by: compiler_referee (P/Q derivation and narrow repair delta)
Baseline: `f9fb4f07c7e045f4a01d70ca4dbf50f93686cce6`
Lease: this file only
Method: constructive inspection of native HIR formation, paired annotation construction, bound replay and the actual typed consumer

## 1. Authority and objective

The governing decisions are [annotation-effect-hygiene-integration](../design/2026-10-10-annotation-effect-hygiene-integration.md) §§1–4 and §6; [concrete-effect-annotation-implementation](../design/2026-10-10-concrete-effect-annotation-implementation.md), “Annotation checking and publication owner” and “Conflict ownership and replay”; and [contextual-attachment-admission-design](../design/2026-10-10-contextual-attachment-admission-design.md) §§3–6. Composed-negative concrete annotations supply function-local subtraction authority; composed-positive concrete annotations supply allowance. Variables retain their connections and do not become concrete annotation atoms. One exact annotation set owns its attachment identity, with member ordinals beneath it; equal nominal support does not merge attachments or contribution instances.

The user withdrew the callback example's claimed result. No expected callback scheme is used. The user also corrected the expansive `my ans: [E] int` witness: this note uses the syntactic function binding `bridge` from the existing Oracle-qualified source evidence.

The primary supplied the later controlling abnormal-path decision during this packet: continue diagnostics where possible, preserve no-wrong-typing and no-inconsistent-publication, abort safely on unrecoverable resource exhaustion, and require rollback only where inference semantics need it. Full internal restoration and exact diagnostic identity are not general abnormal-path premises. P/Q concern successful construction and actual reached consumers; neither depends on the older full-restoration contract. Successful suspension remains distinct from error/abort, and no resumed-suspension theorem is claimed here.

The objective is to establish a bounded actual producer/consumer correspondence for an admitted formal port, and identify precisely why it does not discharge the still-open subtraction obligation. This is neither a new annotation calculus nor another checker assuming source transitions. Complete Call, effect hygiene, soundness, required principality and F5 remain open.

The original quantified hygiene theorem H is stated in
[`Oracle global effect hygiene proof`](2026-10-11-oracle-global-effect-hygiene-proof.md)
§1. This note proves only the local claims P and Q below; it does not restate,
narrow or discharge H.

## 2. Frozen statements, binders and omissions

Fix the existing 28-tail source from [retained-local-capture-observation](../progress/2026-10-11-retained-local-capture-observation.md), “Oracle-qualified source.” For each `i = 0..27`, let `T_i = (int -> [tick, 'e_i] ())`; `ports` is the right-associated arrow chain containing each `T_i` twice. The investigated binding is:

```text
my outer = { my bridge (consume:(ports -> ())) = consume; bridge }
```

`ports` is a metasyntactic expansion, not a source identifier. The Yulang3 prelude is `act tick:\n    our ping: () -> ()`; the Oracle spelling uses `pub act tick` and `pub ping`, with its recorded parameter spacing. The historical frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` accepted exactly the expanded 28-tail source and printed a generalized function scheme. No Oracle run occurred for this note; no claim of acceptance of every smaller or differently annotated source is inherited.

Let `d` be the outer DefinitionRootId; `b` the actual HirLocalId of `bridge`; `s = AnnotationScope::Local(b)`; `a` the parameter annotation; and `p_(i,j)`, `j in {0,1}`, its 56 distinct concrete BracketRow source positions. Let `E` be the declaration-resolved SourceEffectId of `tick`. The lexical function scope `s`, annotation owner `d`, parameter ID, row position and nominal effect ID are separate objects.

**Claim P — bounded constructor characterization.** For every one of these 56 positions, successful execution of the actual FormalAnnotation action constructs a view `v_(i,j)` with allowed members exactly `[E]`, symbolic tail `t_i`, provenance Annotation, owner `d` and position `p_(i,j)`. Within this action, the paired positive/negative interfaces reuse that view; repeated textual `'e_i` uses the same scoped tail, while different positions do not share the view merely because their members/tails coincide. Its effect ports retain Support and Allowance operands at the actual parameter level. No Contribution is created by this construction.

**Claim Q — local replay and check derivation.** Fix one of those views and a canonical effect-row owner `r` during an epoch in which its executable upper bound `Allowance(v)` remains on `r`. For each actual ordinary `candidate_apply_effect` insertion of a lower atom `x` onto `r`, and each actual ordinary insertion of that Allowance against preexisting lowers, the implementation enumerates opposite physical bound operands and supplies newly retained ordered relation-fiber combinations to the typed worklist. Previously recorded combinations need not enqueue again. If a resulting identity-context typed drain reaches the atom consumer, its exact result is:

```text
effect(x) = E  => success, without inserting x into t_i
effect(x) != E => enqueue the same x <: canonical(t_i)
```

Here `x` is either a Contribution instance or an AnnotationMember with its original view/member identity. Support expansion retains each member and the symbolic tail as separate work. This result is a conditional derivation about a reached consumer, not a termination or complete replay theorem. No arbitrary new source arrival is presumed reachable merely because its endpoint can be named.

Shared premises: the supplied source has the recorded HIR formation and source-identity allocation; distinct syntax rows have distinct SourceNodeKeys; candidate feature/session ownership and endpoint branding hold; fallible steps succeed for P, and the selected drain reaches the named consumer for Q. Q's fixed-owner epoch is the unit of this local sublemma, not a restriction on accepted source. Equality/extrusion/fresh-use epochs remain obligations of their actual owners. Neither P nor Q substitutes for the original full hygiene theorem.

For Q's insertion-to-consumer implication, successful physical insertion alone
is insufficient: every fallible replay-setup and child-enqueue operation on
the specified ordinary route must also succeed. If replay setup or enqueue
returns an error after insertion, Q makes no queue-delivery claim; no internal
restoration premise is added.

Exclusions: source operation execution, handler/Catch selection, nonempty contextual subtraction, attachment-qualified residual projection, all-path replay/termination, recursive certificate lifecycle, generalization/use preservation, failure restoration, parameterized effect arguments and public/default cutover. The recorded source reaches a Local use, but that fact does not prove these excluded semantics.

## 3. Derivation of the actual producer

HIR's `source_annotation.rs::parse_annotation_with_marker` (349), `parse_type` (399), and `parse_row` (505) retain the annotation owner/key, recursive type shape and exact row key. `parse_row` resolves `tick` through the declaration namespace to a module/declaration SourceEffectId; it puts `'e_i` in `variables`, not `concrete`. Local formation at `local_source.rs:730–788` creates `b`, retains the parameter annotation with owner `d`, and records its parameter ownership. No effect authority is inferred from the spelling `bridge` or `consume`.

`candidate_source.rs::emit_candidate_source` (167) maps this parameter to scope `s` (184), records its actual level (274), and emits FormalAnnotation before visiting the body (282). Action dispatch calls `candidate_formal_annotation` at line 663. The existing source observation supplies execution of this schedule through formal construction, Lambda formation, local installation and the final Local action; it supplies no hygiene theorem.

`candidate_formal_annotation` (effect.rs:1073) reads the actual parameter row level and enters `candidate_formal_pair(..., Negative, level, ...)`. In `consume:(ports -> ())`, entering each `T_i` uses an Argument Value descent, reversing Negative to Positive. Right-associated outer result descents preserve Negative; the inner Function result descent to `[tick, 'e_i] ()` preserves Positive. Thus every `p_(i,j)` is composed-positive despite the whole formal annotation starting Negative. This follows the actual recursion at 1034–1052, not nearest-textual-port counting.

Each concrete row therefore takes the supported branch of `candidate_formal_effect_port` (1054): call `candidate_signature_effect` twice, with opposite endpoint polarities but the same Positive source variance and shared `views` map. That constructor (1447–1576) obtains `t_i` from `candidate_formal_effect_variable(s, 'e_i, level)` (979), whose registry key is exactly `(scope, name)`. It creates the view once under `p_(i,j)` and reuses it for the other interface. Different row keys produce different views; the shared name key correlates the repeated tails. Endpoint polarity and source variance remain independent.

The positive port receives `Support(v)` as an exact lower bound; the negative port receives `Allowance(v)` as an exact upper bound. Both ports are fresh at the actual parameter level. These are constructor-installed bounds, not claims that an opposite lower already exists or has been checked. `candidate_formal_annotation` then admits the actual value edges at slots 43/44 and retains the negative formal domain. `candidate_scheme.rs::admit_candidate_value_link` (1337) both records the constraint occurrence and calls `constrain_live_value`, so these edges have an executable consumer rather than being provenance-only records.

`candidate_signature_view` (733) retains owner, row key, allowed operands, tail and Annotation provenance. Since a tail exists, `closed_weight` is None. It retains a source-weight/attachment-source record for the Positive source position; `source_weight` (context.rs:2174) stores empty executable left/right words. Its optional SourceUnitPush marker and detached `materialize_unit_push` adapter are preparation, not live subtraction execution. Construction calls no contribution factory. This proves P directly from the selected branches, subject to its declared successful-construction premises.

## 4. Activation and the reached consumer

The Function decomposition in `lib.rs:12493–12563` reverses Argument Value/Effect endpoints and preserves Result Value/Effect endpoints. `candidate_step_function_dispatch` (12643) admits each exact child relation through `candidate_function_port_admit` (context.rs:2557), then enqueues it. The child's inherited input is the actual parent's post-check context; local prefixes remain outside Swap/Preserve. For this tail-bearing Allowance, `candidate_closed_allowance`/`candidate_context_source` (2483/2488) produce no closed filter prefix. Its ordinary supported identity-context path continues to effect dispatch. This is not the zero-word closed-filter discharge case.

Native effect propagation enters `candidate_apply_effect` (extrusion.rs:840) through `lib.rs::apply_effect_task` (11685). For `x <: EffectRow(r)`, it inserts a Positive lower; for `EffectRow(r) <: Allowance(v)`, it inserts a Negative upper. Row-to-row orientation remains selected by levels. `candidate_insert_bound_with_evidence` (406) retains the physical bound, exact admission evidence and origin; the negative Allowance bound also registers its tail capture incidence. That incidence is retained graph reachability for copying, not proof that a lower has run through the Allowance.

`candidate_replay_bound` (763) enumerates the opposite physical bounds. A lower insertion produces `(new lower, existing upper)`; an upper insertion produces `(existing lower, new upper)`. `candidate_context_begin_replay` (2911) visits newly retained lower fibers against all upper fibers, then older lower fibers against newly retained uppers. It preserves ordered parent relations, sharing and Replay dependencies. Where both inputs are Identity, their constructed child is Identity. The retained replay cursor prevents repeating an unchanged fiber combination; it does not select an independent marginal witness.

Crucially, `candidate_context_drive_replay(..., None)` (3110) can return **Queued**. `candidate_context_consume_replay_child` (3060) transfers each item to the typed worklist with a replay acknowledgement; it does not claim that merely generating the batch discharged its children. The typed consumer's Transport/Context/Dispatch stages (lib.rs:12259–12305), or its synchronous worklist loop (11996–12083), retain the actual popped task/relation and call `candidate_context_execute` before dispatch. Identity returns unconsumed (context.rs:2744); effect dispatch (lib.rs:12333) invokes ordinary effect solving when this semantic pair is not already current. Existing current completion can avoid a duplicate semantic check; no new complete-memo/lifecycle theorem is assumed here.

Once the atom comparison reaches `candidate_check_effect_operand` (effect.rs:888), its branch at 919–948 resolves `effect(x)` from the exact Contribution instance or exact AnnotationMember. If E is allowed it returns immediately; if another nominal effect is unmatched it enqueues the *same lower endpoint* against `canonical(t_i)`. It does not insert the matched E into that tail, delete another contribution, or declare the symbolic tail empty. Support expansion (894–916) enqueues every AnnotationMember plus the actual tail. New concrete lowers arriving later at a constrained row enter this same opposite-bound replay path. Hence Q follows for the reached consumer and the specified actual bound insertions. Actual source delivery, complete drain return and all-history memo validity remain distinct premises.

This is the Oracle-inspired current/future-filter bridge for the implemented covariant slice. It does not establish any removal from a handler output. The source witness's returned function value retains support operands; a support member is not an operation event.

Direct inspection of the supplied frozen Oracle checkout `/tmp/yulang2-oracle-read` used `crates/infer/src/lowering/mod.rs:571–663` for Function polarity; `lowering/signature_effect.rs:78–107` for positive row/tail construction, `162–178` for the negative inner-variable/filter wrapper, and `453–460` for excluding annotation variables from concrete grants; and `constraints/machine/bounds.rs:3213–3255,3285–3360` for registering filters on current lowers and checking later lowers. These owners establish why symbolic flow plus later concrete checking is a real Oracle obligation. They do not independently establish this candidate's semantic adequacy, attachment construction, or a literal Oracle-weight migration. Oracle revision identity is supplied by the primary/historical evidence, not revalidated with Git by this leaf.

## 5. The exact still-open obligation

**NEGATIVE-FORMAL-SOURCE-STEP remains OPEN (required A/B).** For each actually formed composed-negative concrete formal annotation occurrence `p` in the accepted semantic source envelope, the owning annotation action must construct its exact function-local attachment set, resolved operands, member ordinals, symbolic connections and source scope; the real effect consumer must implement the selected attached subtraction step for every applicable current/future lower, preserving independent same-family contributions and exact residual/gamma lineage. Its actual copy/extrusion/intrusion/use consumers must preserve that correspondence. Neither a positive Support nor a negative Allowance endpoint from P supplies this conclusion.

At this baseline, the nonvacuous bridge cannot be derived:

| Actual owner | Precise missing premise |
| --- | --- |
| HIR `parse_row` and retained local parameter | Static occurrence, scope and operands exist, but these alone do not establish the operational attachment/contribution relationship. |
| `candidate_source.rs:98,117–121` | Preflight starts a formal at Negative and rejects every concrete row reached with Negative variance. |
| `candidate_effect.rs:1035,1054–1070` | Paired construction independently rejects such a row; it emits no negative concrete formal target/attachment transition. |
| `candidate_effect.rs:1507–1549` | General signature effect construction also rejects negative concrete atoms; the remaining negative branch is direct symbolic flow or empty, not attached subtraction. |
| `candidate_effect.rs:888–958` | The reached atom consumer checks allowance, forwards unmatched atoms or reports mismatch; it has no attachment-qualified subtraction/residual transition. |
| context source-weight adapter | SourceUnitPush preparation is detached; stored markers/weights supply no live nonempty word, relation or discharge step. |

A theorem over “all currently admitted negative concrete formal actions” is vacuous here. The existing [conditional contravariant proof](../progress/2026-10-10-contravariant-effect-conditional-proof.md) and [source audit](../progress/2026-10-10-contravariant-source-bridge-audit.md) already identify this premise. This note supplies a direct executable open-tail covariant construction/check handoff and preserves that obstruction; it does not turn another conditional induction into proof of negative formation.

The proof-obligation-economy audit therefore directs the next work to the construction owner. The missing attachment/consumer agreement is A/B because it implements selected source hygiene and ordinary inference. Recovering that owner from equal row IDs or support sets would introduce D debt: HIR already knows position, resolved operands and lexical binding. Retain and validate those facts there; actual operation/contribution and residual facts must come from their operational owners. Do not reinterpret the missing requirement as optional C, add a source restriction, globally subtract a nominal family, or introduce another reconstruction relation. Authoritative contextual-admission §§5–6 still forbid enabling general concrete-negative formal rows before their later source/admission gate. No enabling patch is proposed by this artifact.

## 6. Transport seam and residual coverage

`candidate_copy_effect_view`/`candidate_remapped_effect_view` (effect.rs:806/832) retain owner, position, nominal members, provenance and attachment-source fields, reconstructing one view per original-ID/mapped-tail key. Ordinary extrusion (extrusion.rs:265–318) uses those mapped views for Support/Allowance/member operands. Capture and fresh use are owned by `candidate_scheme.rs:691,965,981`; their production remapping is at 1054/1062/1097, with physical bound restoration at 1221. These are relevant concrete handoff sites. This note does not establish that their complete relation/residual graph is captured or replayed for a not-yet-emitted negative formal attachment.

Equality may identify solver coordinates without identifying nominal members, view provenance, distinct annotation instances or residual recipes. Current canonicalization (context.rs:3125) retains equality transport witnesses, but P/Q do not prove every qualifying parent/copy SCC case or complete invalidation. No rollback derivation belongs to this packet.

## 7. Evidence, resource use and runtime

Checks performed: bounded `cat`, `rg`, `sed` source/document reads; SHA-256 dependency snapshot below; final leased-file whitespace/link and dependency-stability checks. No code, tests, expectations, configuration or shared records edited. No Cargo, test/build execution, Oracle invocation, executable model, measurement sample, child worker or external recipient. One lightweight shell command at a time except an early batch of independent reads; aggregate CPU/RSS/wall-time was not measured. No heavy process ran.

Workflow nonconformance: the initial orientation command ran read-only `git status --short` and `git rev-parse HEAD` despite this packet's no-Git instruction. HEAD reported the assigned baseline and status was empty at that instant. These are not counted as authorized verification; there were no Git mutations and no subsequent Git commands. Several early broad reads were truncated; derivation relies on subsequent bounded owner reads. Final dependency hashes describe the inspected live inputs; the primary must establish their equality to the pinned revision before integration.

Routing: project config registers prover with absent role model/effort pins and intended Sol/high defaults (`gpt-6.1-sol` / `high`). The leaf's parent launch arguments and effective runtime model/effort metadata are unavailable here: requested launch settings unknown; observed effective settings unknown. No Astra request or execution, model override or reload claim. No delegation occurred. Independent review belongs to the primary; this artifact is a producer derivation only.

One next action: independently review P/Q against these frozen owners, then direct the retained NEGATIVE-FORMAL-SOURCE-STEP premise to the authorized annotation/context source-construction gate. A new checker over supplied attachment flags cannot discharge it.

## 8. Commit packet

- Exact lease/change: `notes/theory/2026-10-11-oracle-effect-hygiene-source-bridge.md` only; writes stop at handoff.
- Baseline: `f9fb4f07c7e045f4a01d70ca4dbf50f93686cce6`.
- Claim/review: unreviewed bounded constructor characterization and conditional reached-consumer replay derivation; no independent certification, semantic authority or parent-gate closure.
- Already checked: static owner reads, dependency SHA-256 snapshot, leased-document whitespace/link check, and repeat dependency-hash check; no builds/tests/Oracle execution.
- Changed dependency hashes: none observed between the two SHA-256 snapshots. Equality to baseline blobs is left to the primary; no additional Git read is authorized for this leaf.
- Proposed message: `research: derive Oracle-qualified formal effect allowance bridge`.
- Shared-record deltas for primary/curator: link this note from the active hygiene lane; distinguish the actual open-tail covariant producer/replay path from detached source-word preparation; keep NEGATIVE-FORMAL-SOURCE-STEP, full hygiene, complete Call, soundness/principality and F5 OPEN. No shared record was edited.

Inspected SHA-256 dependency snapshot (full source file identity; these are not Git blob IDs):

| Path | SHA-256 |
| --- | --- |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-11-retained-local-capture-observation.md` | `61174f1d4e71df401e88116c9cc0ca2090fb4e154ed6c4baac8c1833711934df` |
