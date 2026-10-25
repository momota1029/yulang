# Sprint PAPER-PERFORM-LET-EXECUTION-20261026/r46

Status: READY; Luna authorizes this bounded Lean proof packet inside the user's ongoing inference/executor goal. R44 remains FAILED; R45 remains CLEAN/integrated.
Branch: `research/simple-sub-intrusion`
Baseline: `d1a40e30fae5fe9c9c05500644700ea9868e2a6e`

## Fixed outcome

Construct new module `YulangClosure.PaperTypes.PaperPerformLetExecution`, importing the accepted R45 tuple-split result, to connect the manuscript's perform reduction to request propagation through finite ordinary let frames while preserving the request's **normal result type**. Keep response type, continuation result type, and outer final type as distinct variables.

Prove the following bounded chain for arbitrary shared `D`, graph environment `Xi`, outer type environment `Γ`, operation payload/response types and normal result types:

1. Define an executable operation resolver equivalent to the existing `OperationDeclarationResolved`. It must accept repeated identical declarations and reject conflicting same-identity declarations. Do not use a unique-match-count test.
2. Define the executable perform redex using the same `declaration.instantiate typeArguments` for the emitted `OperationInstance`, payload type and response type. Emit exactly `request instance payload (continuation [] responseBinder (ret (variable 0)))`; preserve the perform computation's response type as the request's normal result type.
3. Define executable request-bind propagation only for the empty-owner continuation produced by perform. Preserve operation instance, payload and response binder. Insert the response binder beneath the stored let body by a typed R28 term substitution: source context `resultType :: Γ`, target `resultType :: responseType :: Γ`, mapping index 0 to 0 and every outer index `n+1` to `n+2`. Use the actual `termSubstituteComputation` result; do not use sequential substitutions or assume an unsupported term is accepted. The original let body must remain in its order after the saved continuation body.
4. Extend R36 finite-control state transitions in this new module only. Preserve push/pop/delegate priority; add perform-to-request and request-through-innermost-frame cases without editing R36. A request with an empty stack is a typed external result; a nonempty-owner continuation is outside this propagation rule. Prove state typing preservation with the same final result type and unchanged shared `D`, `Xi`, and `Γ`.
5. Prove erasure stutter-or-one-step for the new finite control transitions under every stored let frame, lift the request-bind relation through the remaining frames, and prove preservation for every finite transition prefix. No completeness claim for unsupported heads.
6. Prove the empty-owner invariant from perform creation through every request-bind propagation. General owner/handler alpha-renaming stays OPEN.

Source meaning: manuscript perform step `:318–319`; request normal result type and request-bind `:340–359`; ordinary finite let contexts `:1012–1026`; whole parent `:1860–1877` stays OPEN. This packet does not establish that actual corrected full-paper states reduce through this finite let model, nor current-port or residual-graph inclusion.

### Required discriminators

Include checked examples/lemmas for:

- repeated identical declarations resolve; conflicting declarations of the same identity do not;
- operation type-argument arity mismatch returns `none`;
- operation instance, payload, type arguments and instantiated payload/response types use one declaration instance;
- response type, continuation normal-result type, and outer final result type can all differ;
- two nested let frames propagate in order;
- an outer variable beneath the response binder shifts from index `n+1` to `n+2`, while index zero remains the active let binder;
- owner list remains empty; nonempty owners are not silently rewritten.

Examples support but do not replace the universal theorems.

## Frozen sources

- Manuscript `docs/yulang-operational-type-safety-ja.tex`: SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- `PaperTypeFormation.lean`: `29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13`.
- `PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- `PaperTermSubstitution.lean`: `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- `PaperCoreStep.lean`: `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
- `PaperCoreControl.lean`: `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`.
- R45 `PaperTupleSplitExecution.lean`: `7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d`.
- Baseline root `YulangClosure.lean`: `44bc52747836a81fb3d9ae5017d935d3fd9259e2edad8f16b91b48a1c2a5cd0d`.
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`.
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.

Operation resolution authority is the exact existing `OperationDeclarationResolved` in `PaperExecutionSyntax.lean` and `OperationDeclaration.instantiate` in `PaperTypeFormation.lean`. They supersede neither manuscript rules nor source definitions. R28 substitution is the accepted term-substitution operation; no accepted source edits.

## Proof worker lane

One registered `lean_prover`, no children, no Astra. Detached baseline checkout `/tmp/yulang-r46-perform-let`; dedicated `.lake/build` worker-only. Exact write leases in that checkout:

- `notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean`
- `notes/theory/lean/.lake/R46Audit.lean`
- `tasks/agent-loop/inbox/paper-perform-let-r46.md`
- `tasks/agent-loop/inbox/paper-perform-let-r46-worker.log`
- dedicated `notes/theory/lean/.lake/build`

No changes to R45/R36/R35/R28, syntax, typing judgments, root imports, tests, fixtures, expected output, Rust, Git, network, manifest/toolchain, or any other path. Reconfirm frozen pins before and after work. Capture each exact command, cwd, exit, monotonic duration, full raw stdout/stderr and hashes from process launch. Worker cap: **10 literal Lean/Lake calls**, **120 checker seconds total**, **60 seconds per call**, **1200 active seconds**. Include version queries. Stop at first build/audit failure, timeout, pin mismatch, or cap. No repair after a checker failure.

Required strict audit covers every public theorem in the new module: declaration kind, full type, complete `#print axioms`, and `Lean.collectAxioms` whitelist `{propext, Quot.sound}`. Capture all output before handoff. No `sorry`, `admit`, project axioms, unsafe/native bypass, unapproved assumptions, weakened quantifiers or altered accepted claims.

## Luna primary and fresh review

After worker cessation, use `/tmp/yulang-r46-perform-let-primary` at the exact baseline. Verify all pins and exact artifact hashes. Copy only the frozen module and audit source; add exactly one root import in the isolated checkout. Four calls maximum: Lake version, Lean version, default root build with import, complete strict audit. **60 checker seconds total**, 60 per call, 420 active seconds. Capture full raw bytes, command/cwd/exit/duration/hash from process launch; stop on any failure or cap. No Lean in main worktree.

Fresh independent `compiler_referee` after primary evidence freeze; max 180 active seconds; zero checker/build/test/Git/network/write/descendant calls. Review exact source, resolver equivalence (including duplicate semantics), all theorem types and axioms, raw logs/manifest, root delta, source authority, context insertion, finite-prefix preservation and all discriminators. Any blocking/major finding stops integration.

Only after CLEAN review may Luna copy the byte-identical module and isolated root into main, update current state, run `python3 tools/agent_sprint.py check`, and commit/push explicit paths. Do not stage pending questions.

## Scope boundary

No Rust change or implementation bridge is authorized (`NO_SAFE_CODE_SLICE`). General owner/handler alpha-renaming, nonempty-owner request propagation, full-state/current-port/residual-graph simulation, source-owner closure, omitted constructors/frames, native semantics, inference A/B, whole executor, and production remain OPEN. R44 stays FAILED; R45 remains a bounded accepted component only.
