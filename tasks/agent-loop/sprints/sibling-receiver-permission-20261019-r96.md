# R96: compare permission at helper receiver versus captured outer view

Status: ACTIVE; one finite wrong/sibling-permission evidence slice.
Primary: Luna `/root`. This sprint does not adopt runtime permission behavior as language semantics.

## Result sought

Add one paired test in `tools/inference-playground/tests/runtime_receiving.rs` using the existing `IO`, `machine`, `assert_integer`, and `assert_missing_evidence` helpers. Keep the effect family (`io`), operation (`tick`), payload (`7`), outer receiving annotation, nested helper, and call argument identical. Change only the Catch scrutinee name:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my relay (thunk:[io] int) = {
    my helper (pending:[io] int) = catch pending { io::tick(p), _ -> p }
    helper(thunk)
}
my main = relay (io::tick 7)
```

Expected candidate observation: Catching `pending` completes with `7` (the helper's own received view).

Paired negative changes only `catch pending` to `catch thunk`; expected current-candidate observation is `RuntimeUnavailable::HandlerEvidence`. This is a falsifiable runtime-research hypothesis, never a language-level rejection/protection theorem. A surprising result is recorded as evidence and not edited around.

## Proof obligation

Construct a finite source-to-candidate correspondence for both exact sources: original formals and annotation ownership, lexical Name resolution of `pending` and captured `thunk`, retained HIR/Lambda bodies, CandidateInference success, RuntimeProgram construction, invocation and receiving view, then the existing local_grant / Catch selection boundary. State exactly which view the two scrutinees designate, and what the runtime result does and does not establish. Reuse reviewed R88/R92 source facts only where their exact source domain applies. Do not infer native K,D, residual effects, general sibling protection, general permission soundness, or language semantics. Proof note: `notes/theory/2026-10-19-r96-sibling-receiver-permission.md`; handoff: `tasks/agent-loop/inbox/20261019-r96-proof.md`.

## Leases and review

- Luna primary only: this contract, `tasks/agent-loop/current.json`, `tasks/agent-loop/inbox/20261019-r96-spec-review.md`, `tasks/agent-loop/inbox/20261019-r96-compiler-review.md`, and R96 closeout.
- Implementation lane only: add the paired test under a unique name to `tools/inference-playground/tests/runtime_receiving.rs`; no production changes, other files, tests, CLI, or Git.
- Proof lane only: the two proof artifacts above; no source edits, builds/tests/CLI, or Git.
- Fresh spec review before edits; after source and proof freeze, fresh compiler/source review and spec delta confirmation. Reviewers use read-only role constraints and return receipts; Luna archives their exact reports.

## One verification command

After source freeze and spec delta CLEAN, Luna runs exactly once:

`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_receiving <unique_test_name> -- --exact --nocapture`

No retry under R96. The single command must execute both positive and negative examples. Preserve exact outcomes and diagnostics. Compile/runtime failure, expectation mismatch, timeout, source drift, or blocking/major review stops this slice without repair under R96.

## Budget and limits

Total cap 1,800 seconds: proof 600; implementation 360; pre/post spec review 180; one command 120; compiler/source review 240; integration/closeout 300. Astra 0. No budget reset from prior sprints. At most six concurrent identities; unresolved inherited identities and quarantined paths stay untouched.

R96 addresses only one candidate permission-owner contrast. The five other hygiene fronts remain independently OPEN: ordered handler priority; §21 Value/Computation entry; unmatched outward request plus suffix; continuation capture/resumption; static-to-runtime projection. Method/role proof work and R92 runnable effectful source remain priorities in future slices. Original Simple-sub/evaluator claims, A/B quantifiers, R50 and R85 gates remain unchanged.
