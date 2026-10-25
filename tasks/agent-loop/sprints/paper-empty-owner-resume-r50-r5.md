# Sprint PAPER-EMPTY-OWNER-RESUME-20261026/r50 (contract revision 5)

Status: RUNNING; primary-authorized bounded Lean proof packet. Revision 5 adds only exact Luna-owned primary verification output paths. It does not change proof semantics, source authority, baseline, isolation or budgets. Revision 3 records user-directed question withdrawal; revision 2 fixed exact generated-output leases. Calls 01–04 exited 0. Call03 was the module-targeted `lake build +YulangClosure.PaperResumeExecution` (14 jobs, 34.408648903 s), not the default root build. Call04 strict audit took 2.263402532 s. Worker spent 36.776924062 checker seconds; four calls and 83.223075938 checker seconds remain within the original worker grant. The default root build remains primary verification. R49 is CLEAN and
integrated at baseline `e85eb20fd40426316790d1fb543d64b7676b58e8` on
`research/simple-sub-intrusion`. Contract revision r5; supersedes r4 only to add primary stdout/stderr and verification-receipt leases. R4 call03 correction, R3 question status, R2 worker output leases and every proof boundary remain fixed.

## Original outcome and success evidence

Original parent: manuscript `docs/yulang-operational-type-safety-ja.tex`
§複数回 resume と metadata, especially lines 458–466, and the local
preservation claim at lines 1069–1085. The original rule is
`K : Kont(Q,A), v : Q ⟹ Resume(K,v) : A`; each resume freshens bound owners,
substitutes the response, and leaves the saved continuation available for
further independent resumes. This packet represents only the empty-owner
case `K = cont([], x, M)`, where owner freshening is vacuous. It does not
restrict or replace the manuscript claim.

Apply this rule to the actual accepted R49 result: `PaperPerformLetExecution`
`perform_through_stack` (lines 400–426) produces one empty-owner request after
any finite typed ordinary-let stack, with the same operation instance and
final result type. Define a checked response-resume operation on that saved
continuation using R28 `singleReplacement_typed` and the existing computation
substitution relation. Prove applicability and preservation for arbitrary
shared `D, g, e`, response type `Q`, result type `A`, saved body and typed
response `v : Q`. Connect the result directly to the R49 `perform_through_stack`
output. From the same immutable saved continuation, establish two independent
resumptions for any two well-typed responses; preserve the distinction between
`Q` and `A`. Carry the resulting typed states through any finite existing
R49 `Trace` prefix and give the corresponding computation erasure step/evidence.

Success requires a complete strict audit of every public theorem added in the
new module, exact whitelist `{propext, Quot.sound}`, successful build of the
module and default root in an isolated exact-baseline checkout, exact one-line
root import, and CLEAN fresh independent review. Preserve all original
quantifiers and the manuscript's separate fresh-owner case.

## Accepted meanings and fixed dependencies

- Manuscript SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- Root `notes/theory/lean/YulangClosure.lean`: `e2fa0363e9963358a8946f9942f4d2358187272220ddcce5ce89be373089da10`.
- R49 module `YulangClosure/PaperPerformLetExecution.lean`:
  `2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0`.
- R45 module `PaperTupleSplitExecution.lean`:
  `7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d`.
- R28 `PaperCoreStep.lean`: `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
- `PaperExecutionSyntax.lean`:
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`:
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- `PaperTermSubstitution.lean`:
  `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

The exact declarations to reuse are `PaperContinuationTyped` in
`PaperExecutionSyntax.lean`, `PaperCoreStep.singleReplacement_typed`, R28
`PaperComputationTyped.termSubstitute`, R49 `perform_through_stack`,
`StateTyped`, and R49 `Trace`/`trace_preservation`/`erasure`. Read their actual
types before constructing the module. The input/output owner scope is exactly
`[]`; no fresh-renaming theorem may be smuggled in as an assumption.

## Non-goals and source/native boundary

No nonempty owner list, alpha-renaming/fresh-name construction, handler/deep
handler, current-port/residual-graph, full-state source simulation, source/native
correspondence, inference A/B, whole executor or production closure is granted.
No Rust change is authorized. I inspected both actual runtime owners:
`tools/inference-playground/src/runtime/machine.rs` (ResumeArgument, saved
continuation, template capture/entry) and
`tools/inference-playground/src/runtime/continuation.rs` (immutable template
storage). Those owners implement owner/template/activation behavior beyond the
paper-body substitution in this packet; no approved exact correspondence grants
a safe code slice. Record `NO_SAFE_CODE_SLICE` for this sprint. Preserve the
runtime gap as an open source/native obligation.

## Worker envelope and exact leases

One registered `lean_prover`, no descendants and no Astra, in the isolated exact
baseline checkout `/tmp/yulang-r50-empty-owner-resume`. Proof worker may create
only:

- `notes/theory/lean/YulangClosure/PaperResumeExecution.lean`
- `notes/theory/lean/.lake/R50Audit.lean`
- `notes/theory/lean/.lake/R50DependencyCheck.lean` (at most one probe)
- `notes/theory/lean/.lake/build` (dedicated cache)
- `notes/theory/lean/.lake/config` (Lake-generated configuration only; no hand-authored configuration, manifest, toolchain or dependency changes)
- `tasks/agent-loop/inbox/paper-resume-execution-r50.md`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-worker.log`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-01.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-01.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-02.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-02.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-03.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-03.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-04.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-04.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-05.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-05.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-06.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-06.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-07.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-07.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-08.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-call-08.stderr`

The worker may not edit existing modules, root imports, dependencies, source
semantics, audit whitelist, this contract, shared current state, other inboxes,
Rust or questions. Seed and post-work verify all listed frozen pins.

New fixed envelope: **1800 aggregate active seconds, 12 literal Lean/Lake
calls, 180 checker seconds**. Calls 01/02 used 0.104873 checker seconds; resume at call 03 with six worker calls and 119.895127 worker checker seconds remaining. Budgets do not reset. Worker: **1200 seconds, 8 calls, 120 checker
seconds**; primary exact-baseline verification: **420 seconds, 4 calls,
60 checker seconds**; fresh independent compiler_referee review:
**180 seconds, zero checker/build/test/Git/network/write/descendant calls**.
Worker calls each <=60 seconds. Capture each exact command, cwd, exit,
monotonic duration, complete raw stdout/stderr and hashes. Stop at the first
second failed construction build, any final audit failure, timeout, cap,
pin/scope mismatch, or authority conflict. No retry outside the listed calls.
Primary runs in `/tmp/yulang-r50-empty-owner-primary`, never in the main
worktree, and runs Lake version, Lean version, default root build, complete
strict audit only. Luna owns these exact primary evidence paths:

- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-01.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-01.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-02.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-02.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-03.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-03.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-04.stdout`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-call-04.stderr`
- `tasks/agent-loop/inbox/paper-resume-execution-r50-primary-verification.txt`

Capture exact argv/cwd, start/end timestamps, monotonic duration, exit status,
complete raw stdout/stderr byte lengths and SHA-256 in the verification receipt.

## Independent review, integration and stop boundary

Freeze one coherent candidate, audit, full handoff and process evidence. A fresh
independent `compiler_referee` checks source-rule correspondence, exact theorem
quantifiers/types, the Q/A distinction, response substitution under de Bruijn
indices, direct application to R49, two independent resumes from the unchanged
saved continuation, prefix preservation/erasure, complete axiom coverage, all
pins, process evidence and exact one-import root delta. Any blocking or major
finding stops integration; minor findings are adjudicated by Luna.

Only after worker pass, primary pass and CLEAN review may Luna copy the
byte-identical candidate, add exactly one root import, run
`python3 tools/agent_sprint.py check`, synchronize the compact state and
integration receipt, inspect the full outbound range, and commit/push exact
paths. The user directed withdrawal of the two question bundles `questions/2026-10-26-let-bind-input-port-projection/` and `questions/2026-10-26-operational-wrap-graph-guard/`. Luna, as questioner, may write only each bundle's `receipt.md` to record `WITHDRAWN_BY_USER`; preserve each `question.md` byte-for-byte and keep both full directories unstaged/uncommitted. This withdrawal requests no answer and adopts no semantics. R50 workers must not touch either question directory. Preserve all eight UNKNOWN quarantined reservations. R49 remains accepted; full-owner/source/native and
inference parents remain OPEN.


Revision 2 receipt: calls 01/02 exited 0 before the lease spelling issue was identified; no Lean source, audit, build cache, or `.lake/config` was written. Exact call-output paths are individually leased above.


Revision 3 receipt: user-directed question withdrawal is recorded only in questioner-owned receipts. At r3 issuance calls 01/02/03 were preserved, and worker awaited that contract hash. Revision 4 corrects the call03 command from the complete process receipt and records the successful call04 strict audit. No proof claim, source meaning, worker lease, or resource grant changed.


Revision 4 evidence: call04 audited all 18 public theorem declarations, types, kind checks, ordered BEGIN/END markers and full axiom reports; every result is exactly `[propext, Quot.sound]`. Call04 exited 0; no final checker call is pending.


Revision 5 receipt: adds only nine exact Luna-owned primary verification evidence paths; the existing primary grant remains 420 seconds/4 calls/60 checker seconds. No theorem, semantic, baseline, dependency, worker or question status changes.
