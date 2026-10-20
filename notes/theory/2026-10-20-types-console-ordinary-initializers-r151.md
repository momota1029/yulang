# R151 ordinary initializer construction audit

Status: FROZEN revision 1; unreviewed source/native evidence and precise owner obstruction. No CLEAN verdict or parent closure is claimed.

Assignment: R151-ORDINARY-INITIALIZERS-1. Author: `/root/r151_ordinary_initializer_source`; contributing immutable Y2 excerpts and owner lookup: Luna `/root`. No descendants. Source work stopped at the first excluded producer; no production edits, tests, builds, compiler/sample executions, Git or external contact occurred.

## Parent and application

The parent is the unchanged Types/Console outcome in Authoritative `notes/design/2026-10-20-r149-types-console.md`: authentic imported definitions, accepted public inference, retained initialization order and exact host payloads. Types is 142 bytes, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`, requiring `(42, Yulang)\n`. Console is 92 bytes, SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`, requiring `hello from Yulang\n` then `3\n`. These remain a capability increment toward broader unchanged Y2 examples.

The actual progress is a distinction between ordinary binding dispatch, argument-bearing publication suppression and the hidden pattern-binding root. The remaining decisive premise is the actual ordinary-body Evaluation producer, followed by successful declaration-specific publication and imported-root composition. The OpDef route cannot supply that premise. Therefore this evidence supports no sample initializer omission rule, no sample failure claim and no initializer runtime repair. `NO_SAFE_CODE_SLICE` remains the implementation handoff boundary.

Original Simple-sub/evaluator A/B, R70/R71, source/native generality, soundness, principality and production gates remain OPEN with their original quantifiers. F1/FK1 and foreign continuations receive no discharge. Generation, accumulation, propagation, levels, extrusion, qualifying intrusion and generalization are unchanged.

## Frozen inputs and provenance

| Input | SHA-256 |
|---|---|
| R151 contract | `94a16d85418499028a45a40cae434b919942f92eaea9f6a094efa8a0016b0638` |
| R150 rev2 contract | `246edba9d0af7f009e31702ad5ec55db25e491f41bcc20c085e707cb95880657` |
| R150 corrected note, `notes/theory/2026-10-20-types-console-initializer-certificate-rev2.md` | `4e24792cf29bcdc9c6ece8089a9fec17544fbbeaee6182277897865fe969452e` |
| R150 corrected inbox, `tasks/agent-loop/inbox/20261020-types-console-initializer-certificate-rev2.md` | `d821420f59143da1c589665ea983ccf29e4a3ff3b305c29de1c5ec948c04603f` |
| R149 rev5 manifest/contract | `0c44a69e7f6ac5fe32aba8a29b5f439148e99757a0eb31d62f89796ab927d80b` |
| R149 reviewed checkpoint note rev2 | `0ce7e3127519e6a17aeb1f2f6d25b24490fbca4ea3644efaf7e1ea8a7b3420c0` |
| R149 reviewed checkpoint inbox rev2 | `5d786082cabf7b2ce0f9c463eba13c9b1dc9f0cc1ee8e1f8e9d51a4bb03b2ea4` |
| Authoritative R149 design | `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa` |

All SHA-256 values above were independently recomputed from local bytes and matched. Y3 baseline commit/tree are contract-supplied `b7b320d0516208ab4f6aeac14b795f99c6f92cce` / `7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7`. Y2 oracle commit is contract-supplied `a58eefc31e22141574b6f20c6a5748151c6d79f1`; sample owner blob is `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`. No dirty oracle worktree was read. Y2 observations below are explicitly primary-supplied immutable excerpts, rather than independently retrieved whole blobs. The exact 40-library-file manifest is reused within its file-closure premise; it is not an initializer census.

## R150 correction audit

The corrected note and inbox consistently restrict the old constructor trace to OpDef, qualify specialization by success and distinguish DefId from InstanceId. The new primary-supplied `lower_block` excerpt confirms the key path distinction: `SyntaxKind::Binding` and `SyntaxKind::OpDef` have separate dispatch arms. It also confirms that `ExprLowerer::lower_binding_body_expr` exists at the admitted expression owner, but is only a wrapper. The full corrected OpDef body and specialization implementation were not independently retrieved in this leaf; their remaining details retain their supplied/reviewed provenance. This is a bounded audit, not independent certification of R150 or the combined R151 result.

The independently inspected Y3 owners match all five frozen blobs and corroborate the corrected note's local carrier limitation below. The reviewed checkpoint supplies the conditional Y2 Request rejection; this leaf did not independently re-read that runtime implementation.

Minor record finding `R151-R150-LOCATOR-1`: the rev2 note's final resource paragraph still names `tasks/agent-loop/inbox/20261020-types-console-initializer-certificate.md` as its exact new inbox, and the rev2 inbox identifies the old non-rev2 note in its leased-path field. Actual correction identity is the two rev2 paths and hashes in this table. This locator inconsistency changes no source conclusion; Luna owns any sequential correction. No frozen dependency was edited.

Rejected prior use: an OpDef body trace cannot classify ordinary/imported declarations; a lexical file closure cannot become a root census; a nullfix thunk cannot classify all initializers; a root-vector fact cannot prove imported composition order; an assumed body transition cannot prove a source constructor emits it. The withdrawn claim that all initializer requests reach the common host resolver is not restored.

## Actual construction trace and first missing owners

All Y2 entries in the following table use the exact R151 pins. Source locators without line numbers name the supplied symbol, rather than invented line coordinates.

| Stage | Pinned owner | Established excerpt / remaining premise |
|---|---|---|
| Ordinary dispatch | `crates/infer/src/lowering/body/mod.rs`, `f33bdfb5525ddcee02eba9bcd8c181acd1f9ea99`, `lower_block` | `SyntaxKind::Binding => lower_binding`; OpDef separately calls `lower_op_def_body`. |
| Ordinary shape dispatch | Same blob, `lower_binding`, `lower_binding_with_self_alias`, `lower_binding_with_context` | The ordinary path obtains names and argument patterns, selects `lower_single_binding_with_context` for its argument/head-pattern branch and `lower_pattern_binding_with_context` otherwise, with a separate top-level var rejection. No complete parsed declaration join was supplied. |
| Single binding | Same blob, `lower_single_binding_with_context` | Obtains `binding_body_expr`, allocates/registers declaration DefId/root and builds ExprLowerer. Header arguments select `lower_binding_body_with_args_to_named_self`; the other branch selects `lower_binding_body_with_args_to_self`. After successful annotation connection, `finish_binding(decl.def,name,root,computation,!has_header_args)` supplies the publication flag. Thus on this path header arguments suppress root publication regardless of the as-yet-unknown Evaluation. This does not classify every ordinary declaration. |
| Argument-bearing wrappers | `crates/infer/src/lowering/expr/mod.rs`, `5bbedd550c1edf877f4a7c254548ea02f47bcae8`, lines 276 onward | `_to_self` delegates to `_with_self(...,Some(self_value))`. `_to_named_self` introduces an internal local binding, delegates, restores locals and subtypes the result to public_self on success. The actual `_with_self` producer is not in the admitted implementation owner. |
| Pattern/destructuring hidden root | `body/mod.rs`, previous pin, `lower_pattern_binding_with_context` | Creates hidden `#destructure` DefId/root, calls ExprLowerer `lower_binding_body_expr(&expr)`, connects annotation and calls `finish_binding(hidden_def,...,true)`. The hidden root's body Evaluation is unestablished. Projected/generated bindings and their publication paths have not been exhaustively connected. |
| Pattern-body wrapper | `expr/mod.rs`, previous pin, line 271 | `lower_binding_body_expr` returns `self.lower_expr_with_lambda_scope(node,LambdaScope::Defined)`. The actual expression constructor behind this delegate was not supplied; its implementation owner/pin remains unestablished. |
| Evaluation/fetch | `crates/infer/src/typing.rs`, `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be` | Reused R150 supplied evidence: `Computation::value`/`computation` select Value/Computation; `BindingFetch::from_evaluation` maps these to FetchValue/FetchComputation, and only the latter runs computation. No inferred effect-row or RHS spelling replaces this producer fact. |
| Publication | `crates/infer/src/lowering/body/methods.rs`, `086d42bc63f1c12414a42898671dda22c8ac1084`, 293–298, 358–399 | Reused supplied/reviewed evidence: finish/commit stores body and fetch classification and appends `ComputedDef(def)` iff `runs_computation && publish_runtime_root`. Body success and actual Evaluation remain prerequisites. |
| OpDef/nullfix contrast | `body/mod.rs`, previous pin, 2493–2536; `crates/infer/src/lowering/expr/tail.rs`, `8289bfdc6a17b2469ae168ac7939d34813fda474`, 455–476 | Reused corrected evidence: OpDef calls the expression wrapper, optionally applies the nullfix unit-lambda thunk returning Value, then finishes with publication true. This is a distinct path. Methods and other generated bindings remain omitted cases. |

First exact excluded producer for the single/header path: Luna's immutable tree lookup locates `crates/infer/src/lowering/expr/method_body.rs:55::lower_binding_body_with_args_with_self`, proposed blob `70ff50c91b0a93a7aee832ed6b494d933973fe1c`. This path is **not admitted in R151 and was not read**. A sequential exact-pin revision from Luna is required before inspection. The independent pattern branch also stops at `lower_expr_with_lambda_scope`; its owning implementation must be located and admitted before its Evaluation can be asserted.

Applied directly to the parent, these are the next actual source producers to inspect. Merely proving again that Computation plus publication emits a root would leave the same missing premise untouched.

## Declaration joins, composition and native consumers

The authoritative Types text contains `our id x = x`, `pub answer = id 42`, `pub name = id "Yulang"`, `pub pair = (answer, name)` and `pair.say`. It identifies the names and textual shapes, but this audit has no complete parsed-node/DefId join, successful lowering results or imported declaration graph. In particular it does not assert that all no-argument bindings take one observed route. Console's two expression forms likewise supply no imported initializer certificate. Each sample's required imported ComputedDef identities/count, complete composed order and required initializer-to-Request edge remain **UNKNOWN**; zero is not established.

Reused reviewed/supplied owners are `module_map/mod.rs` blob `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6` (stored depth/key traversal), `compiled_runtime.rs` blob `29b400c36a61d5d62aa6518ccb26489d49009898` and `module_table/mod.rs` blob `1b54bd6c9335fbaa1f8b56de9b5014f3d0d17558` (composition owners), `lib_support/specializer.rs` blob `4dfffee1d68b89ea311dd9218bd56d8ab75a42d5` (successful ComputedDef specialization via `ensure_def_instance(...)?` to EvalInstance with InstanceId), runtime `engine.rs` blob `d920a498c226383776ff265d5d8efddd06d06779` and `mono-runtime/src/lib.rs` blob `cb2b4cc1fb563934567a9cdcbaf8f803510372bc` (EvalInstance Request rejection before common host resolution). Their stated local implications remain useful once actual declarations and successful root membership are established. None supplies the missing antecedents, exhaustive composition/cycles or sample impact here.

Independently inspected local Y3 byte hashes were computed as SHA-1 of `blob <length> NUL <bytes>` and matched every R151 pin:

| Owner / blob | Actual observation |
|---|---|
| `crates/yu-hir/src/module.rs`, `d8c3e696734463a7bf63d05da00f77f57b9982f4`, 108–150 | SemanticImports retains optional opaque caller evidence with declaration ownership checks; payload meaning is not certified. No typed imported Evaluation/publication/composed-order carrier appears here. |
| `tools/inference-playground/src/lib.rs`, `9eeaa94180265970a81f9771a7196e4f0d77008d`, 296–307 | Lowering receives SemanticImports::empty(); the same HIR Arc reaches candidate solving. |
| `tools/inference-playground/src/runtime/program.rs`, `fd69daa3d10aeeb4a685766762eef4d80fc0b5de`, 256–308, 625–655 | from_hir iterates HIR items, unwraps Forward/empty Block, classifies Apply/If/Catch/nonempty Block for Definition roots and retains Expression roots. This is a local instruction classifier, with no established equality to Y2 Evaluation or imported publication/order. |
| `tools/inference-playground/src/runtime/machine.rs`, `4bfd5e244a768ef4cfe61b50fff512d5969b3c88`, 292–340 | Source schedule is retained; start validates local definition identities, expression ownership/code and duplicate roots while preserving supplied vector order. It does not construct the missing imported declaration certificate. |
| `crates/yu-solver/src/candidate_source.rs`, `e03d92dcb6016e726fe2748bcfb3f17d52e17cd2`, 1544–1551, 1623–1653 | Separate definition/expression action schedules and source-owner/level checks are present. These inference consumers do not establish Y2 imported runtime publication/composition. |

No Y2/Y3 runtime branch equivalence is asserted. Ordinary inference and residual/provider/witness lineages must be preserved by any later carrier work.

## Exact handoff, falsifiers and STOP

- `R151-ORDINARY-PRODUCER-1`: Luna source owner to grant a sequential exact-pin revision for method_body.rs above and locate/admit the `lower_expr_with_lambda_scope` implementation. Required evidence: real producer outcomes for ordinary/header/pattern paths, then each exact declaration's successful Evaluation, publication and root identity. Falsifier: a required declaration follows a producer/classification/publication path omitted by the claimed census.
- `R151-ROOT-JOIN-1`: Luna module-composition owner to connect those declaration roots through compiled runtime/module-table composition and cycles to successful specialization and actual consumer. Required evidence: complete exact-sample ordered root census; falsifier: an omitted or reordered required root changes acceptance, effects or output. No body-to-Request result may be inferred before this join.
- `R151-CARRIER-1`: Luna implementation owner to consume reviewed source evidence into a bounded identity/classification/publication/order carrier proposal through SemanticImports/HIR, candidate schedule and RuntimeProgram consumers. No implementation is authorized here. Falsifier: differing required Y2 roots/orders collapse to one purported carrier or a foreign declaration identity is accepted.
- `R151-R150-LOCATOR-1`: Luna to adjudicate the stale correction locators above; frozen rev2 hashes remain the intake authority.

Checks: document SHA-256 matching, five local Y3 blob matches and admitted source inspection only. No new/scratch paths beyond this note and the assigned R151 inbox. Source budget: 600 seconds granted; no expansion or carryover; elapsed active work was not instrumented and remains UNKNOWN. Primary charges the issued grant. Requested routing: Sol/high (`gpt-6.1-sol`, high); observed model/effort UNKNOWN/UNKNOWN. The task receipt is the current-session NEW_TASK from `/root`, with subsequent primary excerpt/boundary messages. No descendant or unresolved descendant lease exists.

Writer state: STOPPED after freezing the paired revision-1 inbox. No further source inspection or artifact mutation is authorized under this submission. Next source step requires Luna's sequential pin revision; fresh independent review belongs to Luna. Both the finite parent and production gates remain OPEN.
