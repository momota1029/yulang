# Sprint EFFECT-PERMISSION-ENTRY-LIFECYCLE/20261102-R123

Status: ADMITTED bounded immutable-source lifecycle audit. The standing Rust/Lean soundness goal remains open.

## Objective and parent obligations

Authenticate the source owners left open by R122: whether a real HIR route can form a computation formal with both a record pattern and outer annotation; whether graph/action schedules preserve the guarded `FormalEntry` pre-state; and what errors, rollback, transaction ownership and reuse do after publication. Apply only established facts to existing R39 `ComputationPermissionEntryR39` premises. Preserve the original Simple-sub source domain, effect permission/inflow/subtraction semantics, complete identities and R121's separate consumer-read obligation.

Success is an exhaustive pinned-source owner map plus either a derived reachable lifecycle invariant for a precisely identified entry route or a source-qualified counterexample/first missing ownership edge. Do not infer global safety from constructor guards or local `run_candidate` consumption alone. Do not add a Lean transition model, theorem, source simulation, or change accepted source syntax.

## Exact inputs and leases

Branch `yulang3`; baseline `852ab889cee2f4cfe04da3a1e8c9dd96f9758845`. The manifest `effect-permission-entry-lifecycle-20261102-r123-inputs-r1.json` pins each immutable source and R39 declaration by commit/blob SHA-256. Dirty working copies are excluded; all source reads use `git show` at the pinned commits.

- HIR/source lane: `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/local_source.rs`, `crates/yu-solver/src/candidate_source.rs`; trace all Lambda/formal formation routes and retained fields. Also read-only lifecycle owners: `candidate_scheme.rs`, `lib.rs`, `shadow_apply.rs`, `candidate_effect.rs` at exact manifest pins.
- Proof lane: existing `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` and frozen R122 source/proof handoffs only. No Lean edits or execution.
- Source owner writes only `tasks/agent-loop/inbox/effect-permission-entry-lifecycle-r123-source.md`.
- `lean_prover` writes only `tasks/agent-loop/inbox/effect-permission-entry-lifecycle-r123-proof.md`, after source freeze.
- Luna owns contract, manifest, admission, review, current state, outcome and Git.

## Required coverage and falsifiers

Enumerate every Lambda/formal construction branch and retained AST/local-source field for record-pattern and annotation combination. Trace registration creation, SCC/member/expression scheduling, action ordering and dispatch in both ordinary candidate and shadow-apply paths. Follow all relevant graph/session initializers, caller errors, checkpoint/rollback boundaries, partial publication, consumption/disposal and any graph reuse. Distinguish proof of a local guard from the source reachability law R39 needs; preserve recipe, registration, packed slot, vector index and owner identities as distinct.

Falsifiers include a source-supported combined record-pattern/outer-annotation route; duplicate or reorderable entry schedules; a post-publication error whose graph can be reused without rollback; or any lifecycle fact that cannot be represented by the exact existing R39 inputs. Arbitrary malformed states do not count as source counterexamples.

## Limits, review and resources

No source edits, Cargo/Rust/Lean/Lake/build/test/checker execution, storage/environment probe, cache, target, worktree, scratch copy, or quarantined/dirty-source read. R111 resource gate and runtime serializer quarantines remain unchanged. Keep unknown worker observations and path leases intact.

Caps: source lane 400s; proof lane 300s; fresh `compiler_referee` 180s after both handoffs freeze; Luna 300s; aggregate ≤1,180s; Astra 0. Reviewer checks branch exhaustiveness, source reachability, owner identity, lifecycle failure/reuse, exact R39 mapping and no semantic widening. Commit/push only the exact reviewed R123 records. Stop at the first missing authenticated owner rather than creating another conditional model.

Rust source integration is explicitly **NO_SAFE_CODE_SLICE** under current gates. Existing solver edits remain R111-blocked; runtime files remain quarantined. If the lifecycle audit does not change that authority, keep code untouched and select the next useful in-scope evidence or verified implementation path.
