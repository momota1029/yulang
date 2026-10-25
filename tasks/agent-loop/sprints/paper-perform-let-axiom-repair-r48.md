# Sprint PAPER-PERFORM-LET-AXIOM-REPAIR-20261026/r48

Status: READY; Luna authorizes a new bounded proof and audit packet. R46 and
R47 remain FAILED and immutable. R45 remains CLEAN/integrated.
Branch: `research/simple-sub-intrusion`
Baseline: `334a3892c45518968cbea077a4bb0927c033d020`

## Fixed outcome

Make the frozen R47 candidate eligible for the original strict axiom whitelist
`{propext, Quot.sound}` and produce a complete audit of all 37 public theorem
declarations. R47's final module build succeeded, but its audit failed: 11
declarations reported `Classical.choice`; the audit source also contains an
unsupported `pp.width` option and only emitted 26 of 37 matching END markers.

First locate the actual dependency source for each reported
`Classical.choice`. Do not infer that the resolver is the cause merely because
it was the first R46 build error or because several theorems depend on it.
Use a bounded dependency diagnostic and inspect theorem/helper/library
dependencies. Then remove the non-whitelisted dependency through proof-term
changes alone, using finite-list induction, Boolean case splits or explicit
constructive witnesses where appropriate.

Repair the audit option by removing unsupported `pp.width`; preserve the exact
37-target set, theorem-kind checks, complete types, `#print axioms`, BEGIN/END
coverage and exact whitelist enforcement. Add a separate dependency report
source at `.lake/R48DependencyAudit.lean` if needed to identify direct and
transitive proof dependencies. The original frozen R47 audit remains unchanged.

The candidate's 40 theorem headers (37 public, 3 private), all definitions,
quantifiers, premises, declaration/request semantics, R28 binder insertion,
frame order, empty-owner invariant and finite-prefix statement are fixed.
Only proof terms may change. Do not weaken the exact axiom whitelist or add
assumptions. If removing `Classical.choice` requires a changed theorem
statement, definition, source premise or scope boundary, stop and return a
failure handoff.

Preserve response type, request normal-result type, continuation result type
and outer final type as distinct variables. Preserve repeated-identical
declaration acceptance, conflicting same-identity rejection, same-instance
payload/response construction, request propagation, erasure and all original
discriminators.

## Frozen inputs

- R47 candidate: `fba6990df8444daa163bdc6ec88892bde669072552ac15fef0b26eec81c8e2b7`.
- R47 audit: `8e82040c4345c8c80d73ff1006e9329ad7e6cb8963df5114b2873eb36890f5a1`.
- R47 handoff: `6cff83a0a88463fa7725fcb03ab749a46e4c0baa3139e0efac02e6ebcb6b9b2b`.
- Manuscript `docs/yulang-operational-type-safety-ja.tex`:
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `PaperTypeFormation.lean`:
  `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`.
- `PaperExecutionSyntax.lean`:
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`:
  `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- `PaperTermSubstitution.lean`:
  `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- `PaperCoreStep.lean`:
  `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
- `PaperCoreControl.lean`:
  `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`.
- `PaperTupleSplitExecution.lean`:
  `7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d`.
- Baseline root `YulangClosure.lean`:
  `44bc52747836a81fb3d9ae5017d935d3fd9259e2edad8f16b91b48a1c2a5cd0d`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

## Worker lane

One registered `lean_prover`, no descendants and no Astra. Detached checkout:
`/tmp/yulang-r48-perform-let-axioms`, at the exact baseline above. Luna seeds
the candidate and R47 audit from the frozen inbox artifacts before lease
transfer. Recompute all twelve source/environment pins before and after work.

Exact write leases in that checkout:

- `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean` (proof terms only)
- `notes/theory/lean/.lake/R48DependencyAudit.lean`
- `notes/theory/lean/.lake/R48Audit.lean`
- `tasks/agent-loop/inbox/paper-perform-let-r48.md`
- `tasks/agent-loop/inbox/paper-perform-let-r48-worker.log`
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-*.stdout`
- `tasks/agent-loop/inbox/paper-perform-let-r48-call-*.stderr`
- dedicated `notes/theory/lean/.lake/build`

All other files are read-only. Capture each exact command, cwd, exit,
monotonic duration, complete stdout/stderr and hashes from process launch. The
worker grant is **1200 active seconds, 8 literal Lean/Lake calls, 120 checker
seconds**, at most 60 seconds per call. Calls are allocated to two version
queries, one seed build, at most two dependency diagnostics, at most two
proof-repair builds, and one final strict audit. Dependency reports are
diagnostic only; they do not close the theorem obligations. Stop on a third
failed repair build, audit failure, timeout, pin mismatch, source-scope change
or resource cap. Preserve all failure output; no calls after final audit
failure.

Final strict audit must prove declaration kind, print the complete type and
axiom set for every public theorem, validate all 37 BEGIN/END pairs, and enforce
exactly `{propext, Quot.sound}` through `Lean.collectAxioms`. No `sorry`,
`admit`, project axioms, unsafe/native bypass, unapproved assumptions, weakened
claims or expected-output changes.

## Luna primary and fresh review

After worker cessation, use `/tmp/yulang-r48-perform-let-primary` at the exact
baseline. Verify pins and artifact hashes. Copy only the frozen module and
audit source, add exactly one root import, and use at most four calls: Lake
version, Lean version, default root build, complete strict audit. Cap: **60
checker seconds total**, 60 seconds per call and **420 active seconds**.
Capture full raw output and process metadata at invocation. Stop on any failure
or cap. Do not run Lean in the main worktree.

Fresh independent `compiler_referee` review follows successful primary evidence
freeze; maximum 180 active seconds and zero checker/build/test/Git/network/write
or descendant calls. Review source and proof-only diff, all theorem types and
axioms, dependency diagnosis, raw logs, audit's 37 BEGIN/END pairs, process
manifest, root delta, source authority and discriminators. Any
blocking/major finding stops integration.

Only after CLEAN review may Luna integrate the byte-identical module and exact
one-import root, run `python3 tools/agent_sprint.py check`, then commit and push
explicit paths. Do not stage pending questions. On failure, preserve all R48
evidence, set current state to FAILED, and consult the dispatcher before a new
packet.

## Scope boundary

No Rust change or implementation bridge is authorized (`NO_SAFE_CODE_SLICE`).
General owner/handler alpha-renaming, nonempty-owner propagation, full-state,
current-port and residual-graph simulation, source-owner closure, omitted
constructors/frames, native semantics, inference A/B, whole executor and
production remain OPEN. R44, R46 and R47 stay FAILED; R45 remains the accepted
bounded component only.
