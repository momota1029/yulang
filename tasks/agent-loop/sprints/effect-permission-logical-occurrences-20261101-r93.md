# Sprint R93 — source logical binder occurrence provenance

Sprint ID: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R93`
Status: admitted by primary on `yulang3`; see the paired admission receipt.
Branch / baseline: `yulang3` / `21777269598c0629d31e1b6684c87b0c1eebe724` / `origin/yulang3`
Contract revision: 1
Input manifest: `tasks/agent-loop/sprints/effect-permission-logical-occurrences-20261101-r93-inputs-r1.json`

## Fixed outcome

Construct the logical-binder occurrence inventory directly from unchanged
`OriginalSourceGeneration.sourceRules`. Prove that the actual App `ViewLogic`
and lambda-body `EventProof` entries retain their complete introduction routes,
enclosing binders/telescope, and original source subtree. The original
source-preservation theorem and all of its quantifiers remain unchanged.

The motivating missing premise is R92's source-owned bridge from the generated
source occurrence to an admissible logical payload. This sprint establishes
occurrence provenance only. It does not prove semantic admission, contract
preservation, a joint lift, native correspondence, or the original A/B claims.

Success evidence is a checked Lean module over the small
`OriginalSourceSyntax`/`OriginalSourceGeneration` closure with route-indexed
lookup soundness and completeness, route uniqueness without a distinct-site
assumption, binder/telescope/subtree preservation, and exact App and Lambda
body equations retaining Value/Computation and annotation branches. Every
source constructor remains represented. A missing binder, duplicate complete
route, changed subtree, or dropped telescope entry is a falsifier.

## Lanes and exact permissions

**Proof — registered `lean_prover`, at most 1,000 seconds.** Read only the exact
two source modules and the R92 source handoff pinned by the input manifest.
Write only `notes/theory/lean/YulangClosure/SourceLogicalOccurrencesR93.lean`
and `tasks/agent-loop/inbox/effect-permission-logical-occurrences-r93-proof.md`.
Construct by induction over the generated source tree. Do not edit imports,
root modules, source definitions, Rust, fixtures, or policy. No Git operations.

**Source lane — Luna/primary, at most 600 seconds, read-only.** Trace the
occurrence equations to `ActualKey`, `OriginalFormalAdmission.localAdmissions`
and `decodeFrame`, for both entry modes. Return exact owner-local integration
requirements and identify the remaining semantic law. Write only
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r93-source.md`.
No Rust edits or admission-policy changes.

**Independent review — fresh `compiler_referee`, at most 500 seconds.** Review
the frozen Lean artifact and both handoffs for all constructors, route and
telescope equations, theorem types, axiom audit, exact source mapping and
limited parent application. Write only
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r93-review.md`.

**Primary — at most 300 seconds.** Own current state, exact checker
authorization/receipt if warranted, adjudication, outcome, staging, commit and
push. Aggregate envelope: 2,400 seconds. Astra: 0. At most two direct Lean
checks, each at most 120 seconds, one process, `-M1024`; each exact input needs
independent review and a pushed authorization before execution. No new
environment, worktree, project copy, cache, scratch, Lake build, or tests.
Do not reuse R92's unused second call slot.

## Boundaries and closeout

The only writable paths are the three proof-owned paths above plus the three
primary/source/review handoffs and compact sprint records explicitly assigned
to the primary. All other paths are read-only. Existing UNKNOWN workers and
quarantined leases remain intact. The five current dirty Rust/runtime paths,
the quarantined module-environment handoff, and untracked page-pack artifacts
are excluded from all writes and staging.

The parent source domain, meanings, and quantifiers remain unchanged. No result
here establishes semantic admission or authorizes compiler behavior changes.
Original A/B, source/native correspondence, effect hygiene, principality,
termination and production remain OPEN. Consult the dispatcher at a genuine
counterexample, dependency/lease change, resource boundary, integration seam,
or sprint end.
