# Sprint NATURAL-CONDITIONAL-RESULT-20261024 — preserve heterogeneous branch results through type projection

Status: ACTIVE after primary approval
Branch / worktree / baseline commit / frozen dependency hashes: `codex/natural-conditional-result-20261024` / `/tmp/yulang-natural-conditional-result-20261024` / source baseline `d788d94da66385bf09947932f0aae1972cd51f21`; `scheme.rs` `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0`, `candidate_source.rs` `57b119592a6a8d4afd42aca10c5e2bb749cfdf0fb0fdea967dd437d552a1a04e`, playground `lib.rs` `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4`
Authority: `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §1.1 (both conditional branches constrain the result); `notes/design/2026-10-20-r149-types-console.md` (approved type display behavior); `rules/goal-driven-sprints.md`; actual constructor and consumer source below.
Contract revision / SHA-256 / primary approval receipt: rev1; frozen before producer launch; hash in `current.json`.

## Original outcome and success evidence

Original parent: user goal to implement Yulang type inference and evaluator from established proofs. The original Simple-sub/evaluator A/B, whole-language inference and evaluator remain OPEN; this sprint does not narrow or close them.
Required A/B obligations versus independent characterization: no A/B quantifier is discharged here. The exact ordinary conditional `if true { 1 } else { "str" }` is a selected regression point for the existing approved rule that both branches contribute statically.
Implementation goal: preserve source `If` → both `Action::ValueConstraint`s → graph lower bounds → public `infer_types` projection. Existing runtime conditional continues evaluating only the selected branch.
Success predicates: (1) a written, falsifiable graph-level argument that multiple positive Value lower heads can be displayed together while all upper bounds, shared anchors, quantified Value/Effect identities, permissions and effects remain in the graph; (2) independent proof review; (3) primary implementation in `tools/inference-playground/src/scheme.rs` uses that reviewed generic representation without an If-specific case or constant folding; (4) one bounded affected-package compile check passes; (5) the exact public conditional renders both branch alternatives and existing single-head/open-effect behavior is preserved by the reviewed source argument. Before: `scheme.rs::heads` rejects two distinct concrete Value heads for one row. After: supported multiple heads are rendered as a positive union summary, while original graph constraints remain authoritative. No test is added or run under this contract.
Known open premises/owners: producer proves the exact projection envelope; Luna applies it to the original candidate graph. Structural, cyclic, unsupported or contradictory cases remain explicit errors unless the proof justifies their treatment. General inference completeness/principality, evaluator coverage and source/native adequacy remain separate.
Non-goals: no parser/HIR/solver/runtime semantic change; no new search or inference rule; no head selected by order; no equation of a row with a union based only on lower bounds; no quantified external anchor; no merging distinct effect evidence; no production or parent-gate promotion.

## Two continuing lanes

Proof owner: configured `prover`, exact note `notes/theory/2026-10-24-natural-conditional-result.md` and one inbox `tasks/agent-loop/inbox/20261024-natural-conditional-result.md` in the isolated worktree. Construct the graph-directed projection, cover the conditional and preserved constraints, then apply the result to the selected parent path. Freeze both outputs before review. No author reviews their own result.
Astra: zero assignment; no separate core risk warrants Astra in this bounded projection.
Sol complementary work: fresh independent compiler/spec reviewer after the proof bytes freeze; a reviewer may falsify loss of upper/shared/effect evidence or unsupported union semantics.
Implementation owner: Luna/high, after construction review passes; edit only `tools/inference-playground/src/scheme.rs`. Reads of the solver producer and `infer_types` consumer are pinned to the hashes above. `lib.rs` remains read-only unless Luna approves a revision on concrete evidence.
Provisional evidence: none. Failed/unsupported graph shapes must not silently receive guessed semantics.
Next in-envelope steps: proof construction → independent proof review → primary implementation → freeze diff/dependencies → one independent code-diff review → one affected-package compile check → primary outcome and push of a coherent branch checkpoint.
Reuse: `candidate_source.rs` already emits constraints from both If branches; `scheme.rs` retains the complete candidate graph and currently errors only in display-head collection. Do not repeat historical parser/WhereClause work.

## Permissions and resources

Exact reads: approved authority above; `crates/yu-solver/src/candidate_source.rs`; `tools/inference-playground/src/scheme.rs`; `tools/inference-playground/src/lib.rs`; directly called graph-export/rendering definitions. Exact write leases: proof note and matching inbox to proof producer; `scheme.rs` to Luna only after proof review; contract, outcome, `current.json` and primary Git state to Luna. All worktree source/proof changes remain on the isolated branch while legacy reservations are UNKNOWN_QUARANTINED; no copy-back or merge to the shared research branch without a separately verified handoff.
Runtime/resource envelope: 3000 seconds aggregate active work; proof producer at most 1000 seconds; each independent review at most 300 seconds; primary owns one compile check with a 300-second cap; zero Astra; at most 4 lightweight single-process probes; one heavy Cargo process total. No tests, evaluator executions or additional builds.
Global slots: retain all three UNKNOWN legacy reservations; one proof producer plus primary; reserve reviewer and integration capacity. Do not reclaim any unknown lease.
Stop conditions: reviewed result applied or exact obstruction; source/dependency/authority mismatch; missing permission needed for a new path; any budget cap; user STOP/session end. On stop, record actual write cessation or quarantine the lease.

## Frozen seams and handoff

Proof snapshot: frozen note, inbox, dependency hashes and author list; reviewer must be fresh and independent. Acceptance requires exact graph/source trace, preservation of all original constraints and anchors, correct positive-union reading, explicit unsupported cases, and no claim of principal/accepted schemes beyond evidence.
Code snapshot: only the reviewed proof-enabled `scheme.rs` diff plus unchanged pinned dependencies. Fresh independent compiler/referee review must find no blocking/major issue; any changes invalidate the exact review snapshot.
Parent application: current before/after `heads()` behavior, generic rendered output, both branch constraints and retained graph evidence. Original inference/evaluator A/B stays OPEN.
Dependent production gates: all whole-language and source/native inference/evaluator gates remain OPEN. This result authorizes only this bounded candidate consumer edit.
While proof is reviewed, Luna prepares no source edit to `scheme.rs`; after review, the proof lane stops writing and Luna continues implementation.
Integration: Luna alone stages explicit paths and inspects the full outbound range. Commit/push only the coherent isolated branch; do not merge/copy the branch artifact to the shared research branch while unknown reservations remain.
Current state/outcome: primary-owned `current.json` and this uniquely named outcome. Next dispatcher boundary: proof falsifier/authority change, source mismatch, resource boundary, code review seam or sprint end.
Runtime settings: requested configured prover; observed settings UNKNOWN until runtime reports them. Live identity is recorded only after actual spawn acknowledgement.
