# R147 source handoff — consumer and incoming-state boundary

## Frozen assignment receipt

- Sprint: R147, actual effect consumer and scope protection path; baseline `3560df97dab02744da10e897c73c1cf94118f4ee`.
- Requested role/model/effort: Luna/high. Observed model/effort: UNKNOWN in visible runtime metadata.
- Budget: maximum 600 seconds. No Rust/Cargo/Lean/Lake execution, build, test, source edit, scratch/cache, environment, checkout/worktree, or descendants.
- Sole output lease: this file. No source or other output paths were written.
- R147 contract present at `tasks/agent-loop/sprints/effect-permission-real-consumer-r147.md`, SHA-256 `cc33e831cca0bd86717f0e4c7b995b8f89f2a5418979a66fdbcf0464bb6eeb90`; it is not a blob in the named baseline.
- R146 source handoff was read only as a locator, after its SHA-256 matched `9c940ab56ccd182299833fe93b41701619d600b62c15f3af21b9b94659b694ef`. Its substantive claims were rederived below from baseline source. The R146 proof deviation handoff was not opened or used; its presence is UNKNOWN.

## Admitted input hashes

All Rust hashes below were computed from `git show 3560df97dab02744da10e897c73c1cf94118f4ee:<path>` before source inspection. They match the R147 packet.

| Immutable input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_scheme.rs` | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `crates/yu-solver/src/candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/shadow_apply.rs` | `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278` |
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `notes/theory/lean/YulangClosure/NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `notes/theory/lean/YulangClosure/NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| `notes/design/2026-10-15-compose-scoped-effect-release.md` | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |
| `tasks/agent-loop/inbox/effect-permission-fresh-map-support-r145-source.md` | `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba` |
| `tasks/agent-loop/inbox/effect-permission-fresh-map-support-r145-proof.md` | `da15341b46d3b7adef8cb1bd90d02bfe6dd27fc594a5fb96520f5cf84f82dcea` |

The R146 source locator and R147 packet are frozen artifacts outside the baseline tree and were hashed directly at their listed paths. The named R146 source path is not present in the baseline tree; its current frozen artifact hash matches the packet. No failed `git show` empty-stream digest is treated as an input hash.

## Allocator and support invariant, rederived

`Plan::computation_scope` allocates `EffectScopeId(scope_regions.len())`, then appends that ID to the source scope inventory and its owning region (`candidate_source.rs:155-169`). Scoped Apply collection uses `candidate_calls.calls.len()` as `source_input`, constructs `InputRouteId(source_input)`, and records it in the Apply occurrence's region (`candidate_source.rs:1870-1894`). `ScopeInventory::from_plan` initializes origin vectors with IDs `0..scope_regions.len()` and `0..input_count`, and reconstructs region ownership (`candidate_source.rs:223-245`). Origin values are ancestry data; they are not the injectivity argument.

For each `ScopeInventory::fresh(owned, caller, ...)`, the implementation copies region-owned scopes and inputs. Every copied ID is selected from the current destination vector length immediately before append (`candidate_source.rs:296-357`). Thus successful copied images are distinct within each namespace and strictly above all IDs allocated before that call. `owned` traverses child regions with a seen set, so each region appears once (`candidate_source.rs:272-295`). Failures can leave earlier appends in the inventory before returning an error; those IDs are consumed, not rolled back/reused. No completed FreshUse map is returned for that failed preparation. This supports monotone allocation; it does not prove failure atomicity.

The producers preserve the invariant: initial call seed demand takes its scope from `computation_scopes` and its input from the call index; release takes an existing argument computation scope (`candidate_context.rs:3793-3838`). Function-port conversion uses only demand coordinates (`candidate_context.rs:3924-3987`): ArgumentEffect stamps its input, ResultEffect protects the body scope guarded by that input. Tuple/record/variant ports retain flow. Equality/ordinary transport copies flow; explicit transport changes the demand root, not its scope/input IDs (`candidate_context.rs:3286-3297, 4335-4355, 4650-4668, 4729-4775`). Replay composes existing transformers and carries the upper demand; `ScopeTransformer::then` unions existing finite support without allocating IDs (`candidate_context.rs:4455-4476`, `candidate_scope.rs:131-176`).

`prepare_candidate_fresh_use` calls `ScopeInventory::fresh` once before reconstructing rows and bounds (`candidate_scheme.rs:4444-4451`). Each captured parent flow is remapped using that invocation's one `scope_remap`; transformer and demand coordinates both use the same scope/input maps, with identity fallback outside the copied domain (`candidate_scheme.rs:4773-4800`). Each captured bound consumes the retained per-parent flow for its transport (`candidate_scheme.rs:4861-4907`). `ScopeTransformer::remap` checks injectivity only on transformer-local scope keys and input support, not jointly with demand or any Native `State` support (`candidate_scope.rs:214-258`). Therefore the source constructor chain supports the below-pre-copy-cut invariant for every allocated source/copy coordinate and disjointness of a successful copy image from all prior IDs. It does not construct or authenticate an incoming Native state argument.

## Consumer trace and actual shared route

1. `candidate_context_execute` transports/reuses the task relation, makes it the current `processing` relation, then calls `candidate_context_execute_relation` (`candidate_context.rs:4215-4225`). The relation's `ScopedFlow` is read for the nonidentity/equality guard and, for support/contribution/member effect tasks, stored as a `ScopedObservation` key. That observer stores only `(relation, operand)`; it does not evaluate a consumer state (`candidate_context.rs:4226-4243`).
2. The executor uses the relation's ordinary `ContextId` to compute `candidate_zero_word_filters`. If filters exist, each filter becomes `upper = EffectEndpointKey::Allowance(view)` and the actual task's lower endpoint is retained. An already registered exact upper constructs/replays its bound; otherwise the executor calls `candidate_apply_effect(lower, upper)` (`candidate_context.rs:4244-4291`). Discharge state records the relation and optional residual context, not protection-state evaluation.
3. `candidate_apply_effect` canonicalizes only the two endpoint keys. For row endpoints it chooses an effect-row owner and polarity from the canonical rows' levels, inserts the bound and replays it. For non-row endpoints it calls `candidate_check_effect_operand(lower, upper)` directly (`candidate_extrusion.rs:1147-1172`). No transformer, scope ID, input route, protection list, or `ScopedFlow` parameter is accepted or read there.
4. `candidate_check_effect_operand` makes real endpoint decisions from `BottomPositive`, support-view members/tails, contribution/member effect identity, allowance membership, optional allowance tail, and mismatch reporting (`candidate_effect.rs:1437-1483`). These are concrete effect/allowance decisions, but no Native `State.inputs` or `.protections` participates. The non-row check neither receives protection data nor computes Catch subtraction.

There is a shared route, so “not passed directly” does not mean Catch endpoints are in a separate solver. `candidate_catch_operation` is dispatched from a source `Action::CatchOperation` (`candidate_source.rs:2513`); it builds the continuation/entry effect constraints, including calls to `constrain_live_effect` (`candidate_effect.rs:1181-1287`). The v1 callback-field action also constrains an annotation member against an allowance (`candidate_effect.rs:1307-1353`). `constrain_live_effect` feeds the common `constrain_live` worklist, and candidate-mode `apply_effect_task` dispatches an effect task to `candidate_apply_effect` (`lib.rs:13805-13836`). Consequently Catch-related effect endpoints can traverse the same generic effect propagation route when their task is processed. Static source establishes this common route, not dynamic execution of a particular fixture.

But Catch is not a downstream subtraction consumer of this scoped flow. The Catch action constructs ordinary endpoint constraints and function types; the field-bound action checks an effect endpoint against an allowance. Neither accepts `ScopedFlow`, Native `State`, the FreshUse scope/input map, or a protection set. Their calls can share a candidate graph and worklist with relation propagation; that graph sharing does not itself identify an endpoint constraint with transformer evaluation over a Native state. No Catch subtraction operation was found in this admitted candidate path. `candidate_catch_operation` creates entry and returned effect rows and constrains them; it does not remove a scope from a state.

`evaluate_observation` is the only inspected source call that evaluates a retained scope transformer: it invokes `ScopeTransformer::evaluate(&[], &[])` (`candidate_context.rs:3280-3284`). Its state is therefore empty by construction. It is not called by the effect endpoint or Catch decision above. No inference is drawn from tests or runtime output.

## Parent/native correspondence and first missing boundary

The authoritative compose decision says release the `'e` protection on the matching contribution within output `'f`, including forwarding `f = id`, while preserving contribution attribution and other protections (`notes/design/2026-10-15-compose-scoped-effect-release.md`, “Scope of the operation”). Native `Transformer.evaluate` changes `State.inputs` and `.protections`; its rename law requires the same injective scope/tag maps to cover both transformer and incoming state (`NativeScopeTransformer.lean`, `renamed_protection` / `evaluate_rename`). The conditional R145 proof handoff also requires supported transformer and state coordinates below the pre-copy counts; it is unchecked and supplies no source instance.

The source has a transformer/demand flow and endpoint decisions, but no authenticated owner that supplies the *actual incoming* `NativeScopeTransformer.State`, renames that state's relevant support under the exact FreshUse map, and connects its protection membership to a real effect/Catch outcome while preserving the same contribution witness. Demand and `use_instance` are not substitutes for `State`; empty observation state is not the incoming state. The first missing bridge owner is the source consumer path joining relation/FreshUse evidence to effect eligibility or Catch release, with an explicit state carrier and same-map transport. No extra source file is required to state this boundary; any further source owner must return to Luna for an authority decision.

Concrete falsifier for this source-boundary finding: admitted production code contains a reachable effect/Catch decision that reads the actual incoming input/protection state (or an authenticated encoding of it), carries those exact coordinates through the same FreshUse map, and changes the consumer decision according to that state while retaining the same source contribution. For the allocator premise, a reachable producer with an incoming transformer/state coordinate at or above the pre-copy inventory cut, omitted from the same copy map but identity-fallback retained, would falsify the below-cut premise. Neither falsifier was found. Their absence here is not a counterexample to the original A/B claim.

## Evidence disposition, checks, and stop

- R145 source handoff was reused only as a locator for the single FreshUse remap and identity-fallback sites; I rederived the allocator and producer path from the R147 baseline. R145 proof handoff was read as a conditional unchecked candidate; it is not source evidence or theorem closure.
- R146 source handoff was a locator only. Its allocator and empty-observation claims were rechecked against admitted baseline blobs. R146 proof deviation observations/conclusions were excluded and not opened.
- No withdrawn Simple-sub bypass was restored or considered. No semantics, source domains, expectations, diagnostics, compiler sources, or proof files changed.
- Read paths: the nine listed `crates/yu-solver/src/{candidate_source.rs,candidate_context.rs,candidate_scheme.rs,candidate_scope.rs,candidate_intrusion.rs,shadow_apply.rs,lib.rs,candidate_extrusion.rs,candidate_effect.rs}` baseline blobs; both listed Lean blobs; the compose design note; R145 source and proof handoffs; R146 source locator; and the R147 contract. All Rust inspection used `git show` at the exact baseline. No tests/checks/builds/execution ran by contract.
- No additional or disposable scratch path was created. The sole new path is this leased handoff. No source, proof, cache, generated, or scratch outputs were created. The handoff is frozen; writing stops here.
- Full source/native theorem, original A/B claims, semantic approval, and production readiness remain OPEN. Independent review is required; this author does not certify the handoff.
- Next related in-envelope step: independent reviewer checks hashes and rederives the endpoint/Catch shared route and state boundary against the baseline, then Luna adjudicates the source/proof seam. Do not promote from this source trace alone.
