# Oracle producer crosswalk after erasing representation

Date: 2026-10-06
Status: independently compiler-referee/spec-auditor-reviewed historical characterization
Claim class: historical mechanism characterization; no semantic or implementation authority.
Current authority baseline: `d07fa561c15e66875aefb4092827a7030e736a81`.
Frozen historical source: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
Integration baseline: `f1fc1a6eb700b1406d6bedebb46aec7cad082774`.

Companion: [main source-generation localization](2026-10-06-main-source-generation-minimal-clause.md).

All abbreviated historical paths beginning with `lowering/`, `annotation/`, or
`instantiate.rs` are relative to `crates/infer/src/` at the frozen revision.

## Result

Common formal identity, environmental retention and coordinated use-time renaming are concrete historical mechanisms, and their current preservation requirements are already selected. Replacing Oracle's mutable variables, levels, bounds and subtraction IDs with another representation does not reopen those requirements. The remaining source producer is smaller than an unspecified inference algorithm: an interpretation of source-owned atomic evidence that produces **one joint admissible formal/use relation together with typed original incidence/profile and receipt schemas**, before the comparison which will consume them. The source-atomic clauses for the unannotated Handler seed, its ordinary-value refinement and annotation-contribution attribution remain unspecified. A satisfying-assignment definition becomes legitimate only after those atoms and their joint interpretation are supplied.

A concrete additional bridge is a durable annotation-derived formal contract omitted from the two assigned October 6 archaeology notes: `ArgEffectContract`, created from a parameter annotation, stored by formal `DefId`, recovered by callee declaration and argument position, and consumed in argument-boundary hygiene. This does not supply the current profile. It does show that a static source annotation certificate can travel beside generalized types rather than being reconstructed from their shape.

During this submission's review, upstream `2d378d0c` added the independently
reviewed [argument-effect contract channel](2026-10-06-frozen-oracle-argument-effect-contract-channel.md).
That convergent characterization is incorporated as existing evidence, not a
separate new semantic result. This crosswalk also identifies the distinct
Scheme/sidecar preservation channels and equivalent-Function boundary branch.

## Evidence and authority boundary

All historical paths below are at the exact frozen SHA. New direct reads used `git show` in `/workspace/scratch/5818f4c07d78/yulang`; that checkout contains the historical object. The assigned current checkout does not contain it, and `/tmp/yulang2-oracle-rebuild` is absent in this environment. No build, source execution, Git mutation, source write or agent delegation was performed. The prior rebuild note proves three old-side CLI observations at its own inspected snapshot; this report makes no new source-acceptance claim.

Current authority is `notes/design/2026-10-05-inferred-function-call-views.md`, especially lines 93–114 (shared source relation, typed incidences and comparison-independent admission), 118–134 (the selected provisional Handler/ordinary-value direction), 138–151 (annotation-scoped permission), and 158–184 (open exact judgments and proof gates). The exact returned-closure interpretation remains the nested-block addendum, §§2–3. Historical algorithms do not supply authority.

## Six-part crosswalk

| Requirement | Historical source witness | Representation removable | Current input/output clause still required |
| --- | --- | --- | --- |
| Formal endpoint sharing | `lowering/expr/lambda.rs:664–741` allocates/install parameters and frame metadata; `lowering/name_ref.rs:146–169` resolves fresh use `RefId` to the same local `DefId`; `lowering/expr/tail.rs:855–858` returns the live endpoint when no scheme exists. | `TypeVar`, vector layout, ID number, arena pointers. | Resolve each use to its binder; retain that common symbolic root and original static identity through the component. This is forced preservation, not a fresh semantic choice. Shared root alone is not a completed Function relation. |
| Application constraint production | `lowering/expr/tail.rs:543–563` obtains argument value/effect endpoints, a return-effect view and result endpoint, then relates the shared callee endpoint to one four-port Function demand; `:615–627` composes callee/return effects and emits App (the latter locator is supplied by the reviewed prior archaeology). | Polarized nodes, bound insertion, worklist scheduling, fresh-result allocation mechanism. | At each resolved call, interpret callee, whole argument, return and effect incidence on the same joint assignment. Existing conditional complete `J_call` composes already decorated inputs; it does not introduce their original typed incidence. An ordinary call demand is not exhaustive membership/admission. |
| Environment-aware generalization | `lowering/expr/tail.rs:951–969` drains work or retains a live endpoint when relevant selections are unresolved; `:970–1011` generalizes with environmental constraints and stores scheme/provenance; `:1014–1040` retains other locals and their bound-connected variables. | Type levels, bounds-table traversal, `non_generic` hash set, snapshot/drain implementation. | Preserve external binder relationships when packaging a local scheme; do not quantify a captured outer endpoint into an independent witness. Current complete source-relation preservation/principality is not proved by the legacy retention mechanism. Broader local polymorphism is outside the exact nested-source decision. |
| Coordinated freshening | `instantiate.rs:620–648` freshens quantified/recursive/stack identities before cloning common predicates; `:732–760` memoizes renaming and leaves unmapped variables unchanged unless instructed otherwise. | Actual variable/subtraction IDs and memo map implementation. | Rename each generalized coordinate consistently throughout its joint relation, keeping non-generalized/environment references and original source identity. Per-port independent witness choice violates the selected relation; no new algorithm choice is needed to see that. |
| Provenance routing | `lowering/expr/tail.rs:861–940` reads generalized witnesses, retains path/completeness, records a use with original scheme/parent/definition/root, and emits routes carrying the source witness and remaining path. | Route list/table layout, counters and diagnostic IDs. | Original typed paths and their complete source/owner/receiver correspondences must be generated and preserved. Oracle provenance can be explicitly incomplete; source-witness paths are not automatically current `Slots(beta)` or admissible receipt paths. |
| Annotation and function-frame production | `annotation/builder.rs:13–27,123–143` uses one annotation scope and distinguishes parameter value, argument effect, result effect and result value; `annotation/constraints.rs:251–284,363–390,424–470` connects parameter-specific and Function bounds; `lowering/expr/lambda.rs:724–736,852–863` associates locals with definition frames and wraps results. Durable sidecar contract is detailed below. | Temporary `AnnType`, IDs, push/pop implementation and frame container. | Relate the actual annotation occurrence and its permission to the particular original protected contribution, retaining unrelated contributions/evidence. Also state how absence produces the approved internal protected seed and how the ordinary-value use refines it. Oracle's subtraction recipe does not define those current atoms. |

The table does not establish complete old-to-current correspondence. Direct reads confirm every listed source window except the explicitly marked prior `tail.rs:615–627` window. No global absence claim follows from the selected structures.

## Additional concrete annotation witness

### Creation and persistence

`lowering/expr/lambda.rs:1244–1264` distinguishes no source annotation from an annotation: absence sets `argument_effect_contract: None` and marks `Unannotated`. With an annotation, `:1266–1307` builds it and threads the same annotation-variable and closed-effect-row maps through its constraint lowerer; `:1327–1340` separately computes the argument contract and marks `Annotated`.

`lambda_annotation_argument_effect_contract`, `:1357–1366`, constructs the sidecar only when the root `AnnType` is Function. `collect_argument_contract_markers`, `:1369–1409`, walks the annotation: each Function increments a nesting depth, visits both argument/result effect rows and recurses through parameter and result; tuple/application arguments keep the current depth. `:1413–1434` emits a deduplicated marker for each named effect atom:

```
(effect-family path, Function nesting depth, PreserveMatchingPath)
```

`effect_contract_path`, `:1437–1448`, resolves builtins/named declarations to family paths and uses an applied type's callee path. This marker projection does not retain that effect application's type arguments.

`mark_lambda_param_effect_contract`, `:896–908`, obtains the actual formal `DefId` from its pattern and writes `poly.arg_effect_contracts[def] = contract.clone()`. `crates/poly/src/expr.rs:76–81` explicitly documents that source-annotated arguments form a separate contract from `Def::Arg` and that downstream hygiene must not reconstruct that distinction from mono type shape. The marker structure and resume-policy enum are at `:147–163`.

This is durable formal-keyed source evidence, not only temporary `AnnType` or accumulated frame weights. The two assigned October 6 archaeology notes do not mention `ArgEffectContract` (bounded literal search), but an older note already located its downstream consumer: `notes/progress/2026-10-01-intrusion-coarse-effect-abstraction-candidate.md:2802–2827`. Novelty is the complete producer/storage-to-known-consumer connection and the exact losses in this schema, not discovery of an entirely unknown Oracle mechanism.

### Generalization and use-time transport are separate channels

`crates/poly/src/types.rs:17–23` lists all Scheme fields; `ArgEffectContract` is absent. The directly read local generalizer (`tail.rs:944–1040`) records a scheme and source witnesses and does not transport this contract. `instantiate.rs:620–648,732–760` clones predicates with coordinated renaming, while a bounded whole-file search finds no `ArgEffectContract`/`arg_effect_contract` reference in that file.

The contract instead survives by stable definition identity. Local name lowering still emits `RefId -> local.def` even after `instantiate_local_value` (`name_ref.rs:153–168`). The downstream consumer recovers original declaration/formal identity from that reference and its call position, independently of the instantiation variable map. This explains two different preservation obligations: consistently rename generalized relation coordinates; retain the original source declaration certificate. It does not prove arbitrary alias, imported contract, captured-provider or higher-order transport.

### Call consumption

`crates/specialize/src/specialize2/emit.rs:248–266` handles App, recovers the callee's argument contract, and passes it to the argument boundary wrapper. `callee_argument_effect_contract`, `:1149–1162`, finds the call-spine head and already-applied argument index. `:1173–1182` counts App nodes. For a reference it resolves the head to the declaration; `:1192–1206` requires a `Def::Let` body beginning with Lambda. `:1209–1231` follows the lambda chain to the indexed parameter and reads the formal-keyed sidecar.

Thus this mechanism does **not** read `arg_effect_contracts[f]` when the callee is the formal `f` in an internal `f x`: the referenced definition is `Def::Arg`, so `:1197–1201` returns None. It reads the contract for supplying a callback to a known declaration/lambda parameter. A separate guarded unannotated-formal call/frame mechanism exists at `tail.rs:740–798`, as characterized by prior archaeology; the two routes must not be conflated.

`emit.rs:1013–1049` carries the recovered contract into a checked runtime boundary constructor. Its direct helper is **`crates/specialize/src/specialize2/runtime_shape.rs:875–905,996–1006`**: it emits a FunctionAdapter with `function_adapter_hygiene_with_argument_contract`, including when function boundary types are equivalent but a contract is present. Thus equal runtime type shape does not erase this source certificate. `crates/specialize/src/hygiene.rs:15–35,62–89` converts its markers into argument guard markers. A `PreserveMatchingPath` marker becomes `(family path, depth, guard_own=true, guard_foreign=false, preserve_own_on_resume=true)`; `:499–524` combines duplicate family/depth markers by OR-ing flags. A separate older specializer channel also passes the contract to hygiene (`crates/specialize/src/lib_support/specializer.rs:305–332,408–418`) and can call `lib_support/boundary.rs:106–112`; that older helper is not the direct Specializer2 dispatch. Runtime execution, full backend selection and successful source paths were not tested here.

### Algorithm-independent historical finite schema

Erase the implementation types and ID numbers. The inspected producer computes:

```
formal source annotation
  -> resolved finite named-effect/depth marker set
  -> certificate attached to that original formal

known declaration/lambda and next argument position
  -> corresponding formal certificate
  -> argument-boundary hygiene contribution
```

Finiteness follows from traversal of the supplied finite annotation tree and marker deduplication. It is an implementation characterization, not a finite-source theorem for arbitrary current components.

What survives erasure is the distinction between **source annotation certificate** and **inferred type shape**, its attachment to a formal, and its routing through an actual known argument position. Family/depth is insufficient as a current typed path: the producer visits parameter/result branches at the same depth, drops type arguments, deduplicates occurrences, and carries no annotation occurrence ID, branch selector, original slot/profile, role/entry, owner/receiver incidence, actual receipt or whole joint fiber. None of those losses can be justified by replacing IDs with new names. Conversely, requiring a particular legacy `SubtractId`, depth stack or adapter policy would import an unapproved algorithm and semantic behavior.

## Smallest missing current source relation producer

For the exact unannotated captured-step component, lexical interpretation already supplies binder/use/call/capture incidences and the core prefix supplies shared symbolic endpoints. The conditional complete invocation constructor is supplied separately (source-call-image note lines 23–46). Do not ask for another endpoint-allocation, generic registration record or solver worklist.

The next necessary local relation clause has inputs:

```
original formal d_f and its source/contract scope;
resolved use u_f -> d_f and call c;
ordinary whole-argument derivation u_x -> d_x;
absence of annotation at d_f;
one shared endpoint naming and relevant source component.
```

Its output must specify, before Q:

1. Which original role-indexed formal/use relation rows the absence-caused protected seed and this ordinary-value evidence permit; how the selected non-Handler refinement constrains those same rows while preserving supplied callable roles/entries.
2. Which original typed call/receipt/profile incidences those rows carry, using the resolved source occurrences and scope rather than their solved shape. This is a static receipt schema; a later actual provider/receiver event requires a distinct typed instantiation.
3. How those row conditions constrain one whole `xi=(nu,K,D)` and are admitted independently of Q. The ambient admitted relation/profile cannot be inferred by selecting successful comparison rows.

This is a **missing exact formalization of already selected semantic input/output constraints**, not proof that the language meaning is undecided or that a specific inference algorithm is necessary. The authority expressly leaves the two-stage judgment and full admission producer open. A candidate can parameterize remaining actual role/entry resolution while deriving its source-owned evidence relation; it cannot postulate an already completed formal contract and call that source generation.

For annotated variants add only the corresponding atomic clause: resolve the annotation occurrence, relate its named permitted contribution to the original typed position/contribution and its realization evidence, and state when permitted removal is realized. The durable Oracle sidecar suggests a concrete separation of certificate creation and call routing, but its family/depth schema and resume policy cannot be adopted as current semantics.

After those atomic interpretations exist, conjunction/natural join over the **same** original coordinate assignment, environmental packaging and coordinated renaming are plausible compositional constructions. Their preservation proof remains necessary. Defining `Omega_S` as satisfying assignments is circular only while the source atoms and typed-incidence interpretation remain unconstructed; it is not inherently circular once they exist. Exhaustive Option A/Option 2 production admission, production-only members and adequacy/principality are distinct later checks.

## Contradictions avoided and questions retained

- Oracle four-port bounds, `Empty` subtraction facts and push/pop weights do not identify a current Handler seed. The approved unannotated seed is internal evidence and full protection is not an empty row.
- Legacy `RolePredicate` in Scheme is documented as type-class-like residual role constraints (`poly/types.rs:35–44`); its name is not evidence of current Pure/Handler callable-role indexing.
- Historical annotation `Function` construction and closed-row interning (`annotation/constraints.rs:363–390,602–619`) do not authorize forming typed current paths/profile by equal type/family shape.
- The stored annotation marker route proves source distinction persists beyond solving; it does not prove complete typed receipt/capture transport or preserve a dynamic receiver after expiration.
- The exact captured-step source decision does not select broader recursive closure or local-polymorphism behavior. Their environment-sensitive old machinery is characterization only.
- Remaining question is whether the next proposed local evidence interpretation actually derives full admitted relation/profile rows with the selected seed/refinement and permission semantics. Testing consequences of a stipulated completed relation will not answer it.

## Checks and limitations

Mandatory policy and five assigned notes were read; current authority was read with exact locators. One bounded Python script located the frozen object in existing checkouts (about 15 seconds, no compute search); source reads were static `git show`/line windows and limited literal searches. Some initial captures were truncated; decisive windows were recovered narrowly. The producer did not certify its own report. Subsequent independent compiler-referee/spec-auditor reviews found no blocking or major issue in the stated historical/current separation; the spec review also directly checked the inherited `tail.rs:615–627` window. No current acceptance, soundness, principality, complete source adequacy, end-to-end runtime transport or production-conformance result follows. The archaeology producer wrote only its isolated scratch report; the primary integrated this frozen research record. Independent certification is recorded in [the review record](2026-10-06-main-source-generation-review.md).

Frozen original-source SHA-256, computed from `git show` output:

| Exact historical path | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/poly/src/expr.rs` | `fbee59668b778c09cf32ad5b59c919feb36726b1af75cb630bca1ca9b7aebd88` |
| `crates/poly/src/types.rs` | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| `crates/specialize/src/specialize2/emit.rs` | `7318b132cef4217ae089d084577fb28f3abed34a5728474ee8569e4079d71e7c` |
| `crates/specialize/src/hygiene.rs` | `266c05f4c937fc9f9d95cb6b1c435e9ff74181ffc5e8d7719faeefc7a8ff33e4` |
| `crates/specialize/src/lib_support/boundary.rs` | `10e7f3fa637eb35f5b4097aca9c0ede30672110ecb14a77b0cce9757ad5bcf1d` |
| `crates/specialize/src/specialize2/runtime_shape.rs` | `e4443fa1c23a1ea0d957d4582f484abea53e1aa0dffe2f86a3f44fc70aa2e0e4` |
| `crates/specialize/src/lib_support/specializer.rs` | `6efdb58c5c3ea99506a45b4b5f726775b03352421bb8b4fefe36cc4762e3eeef` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
