# Sprint PAPER-PERFORM-LET-REPAIR-20261026/r47

Status: READY; Luna authorizes a new proof-construction packet. R46 remains
FAILED and immutable. R45 remains CLEAN/integrated.
Branch: `research/simple-sub-intrusion`
Baseline: `d0d57a893faccde663d32c50f0416b8c244c726c`

## Fixed outcome

Repair the proof terms in the frozen R46 candidate
`tasks/agent-loop/inbox/paper-perform-let-r46-candidate.lean` so the existing
perform/request-let bounded chain compiles and receives a complete strict
audit. The definitions, all 37 public theorem statements, premises,
quantifiers, and empty-owner boundary must remain byte-for-byte structurally
unchanged. Proof terms alone may change.

The first build exposed elaboration failures, not a mathematical
counterexample. Repair only these proof-construction issues:

1. `resolveOperation_iff`: split the Boolean `all` result explicitly and avoid
   broad `simp` rewriting that loses the negative test hypothesis.
2. Request construction: provide declaration, type arguments, operation
   instance, payload, response binder and continuation explicitly; do not rely
   on `apply` goal ordering.
3. Give explicit owners, binder and body for existential request witnesses.
4. Reduce `Option.bind`/do notation explicitly where the restricted
   simplifier does not unfold it.
5. Remove variable names from nullary `refl` induction alternatives.

If any theorem statement, definition, accepted source premise, or scope boundary
must change, stop and return a failure handoff. Keep response type, request
normal-result type, continuation result type and outer final type distinct.
Preserve duplicate-identical declaration acceptance and conflicting
same-identity rejection. Use the same instantiated declaration for operation
instance, payload and response. Preserve R28's simultaneous binder insertion,
frame order, finite-prefix typing, erasure, and the owner-empty invariant.

The original R46 failed candidate is a seed, not accepted evidence. R46 remains
FAILED regardless of this packet's result. No theorem is accepted before the
complete audit and independent review.

## Frozen inputs

- R46 candidate: `531703d7a66a87277489e9d7c6775de68cdfcd23d8096770ddb0e41c62180262`.
- R46 audit draft: `8e82040c4345c8c80d73ff1006e9329ad7e6cb8963df5114b2873eb36890f5a1`.
- R46 handoff: `f692e59c9d1cddf3fafc90746677ce0742b313c8317ca0e5bc9194e07610b901`.
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
- R45 `PaperTupleSplitExecution.lean`:
  `7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d`.
- Baseline root `YulangClosure.lean`:
  `44bc52747836a81fb3d9ae5017d935d3fd9259e2edad8f16b91b48a1c2a5cd0d`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

## Worker lane

One registered `lean_prover`, no descendants and no Astra. Detached checkout:
`/tmp/yulang-r47-perform-let-repair`, at the exact baseline above. Luna seeds
the module with the frozen R46 candidate before lease transfer.

Exact worker write leases in that checkout:

- `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean` (proof terms only)
- `notes/theory/lean/.lake/R47Audit.lean`
- `tasks/agent-loop/inbox/paper-perform-let-r47.md`
- `tasks/agent-loop/inbox/paper-perform-let-r47-worker.log`
- the dedicated `notes/theory/lean/.lake/build` and enumerated process logs

All other files are read-only. Recompute every frozen pin before and after work.
Record exact commands, cwd, exit, monotonic duration, complete stdout/stderr and
hashes from process launch. Include version queries in the call count. Worker
grant: **1200 active seconds, 10 literal Lean/Lake calls, 120 checker seconds**;
at most 60 seconds per checker call. Up to two failed construction builds may
guide proof-term repair. After them, stop on another construction failure.
Reserve one successful final candidate build and one complete strict audit.
Any audit failure, timeout, pin mismatch, source-scope change or cap stops the
packet. Never change the theorem statements or definitions to make a proof pass.

Strict audit covers every public theorem: declaration kind, complete type,
complete `#print axioms`, and `Lean.collectAxioms` whitelist exactly
`{propext, Quot.sound}`. No `sorry`, `admit`, project axioms, unsafe/native
bypass, unsupported assumptions, weakened claims or expected-output changes.

## Luna primary and fresh review

After worker cessation, create `/tmp/yulang-r47-perform-let-primary` at the
exact baseline. Verify all pins and artifact hashes. Copy only the frozen module
and audit source there, then add exactly one root import. Four calls maximum:
Lake version, Lean version, default root build, complete strict audit. Cap:
**60 checker seconds total**, 60 seconds per call, **420 active seconds**.
Capture full raw outputs and process metadata at launch. Stop at any failure or
cap. Never run Lean in the main worktree.

Fresh independent `compiler_referee` review follows primary evidence freeze;
max 180 active seconds, zero checker/build/test/Git/network/write/descendant
calls. Review exact source, proof-only diff, all theorem types and axioms,
logs, primary manifest, root delta, source authority, resolver duplicate
semantics, context insertion, frame order and discriminators. Any
blocking/major finding stops integration.

Only after CLEAN review may Luna integrate the byte-identical module and exact
one-import root, run `python3 tools/agent_sprint.py check`, and commit/push
explicit paths. Do not stage pending questions. On failure, preserve R47's
candidate and complete evidence as inbox artifacts, set current state to FAILED,
and consult the dispatcher before another packet.

## Scope boundary

No Rust change or implementation bridge is authorized (`NO_SAFE_CODE_SLICE`).
General owner/handler alpha-renaming, nonempty-owner propagation, full-state,
current-port and residual-graph simulation, source-owner closure, omitted
constructors/frames, native semantics, inference A/B, whole executor and
production remain OPEN. R44 and R46 stay FAILED; R45 remains the accepted
bounded component only.
