# Sprint PAPER-TUPLE-SPLIT-EXECUTION-20261026/r44

Status: READY; Luna authorizes this bounded proof packet within the user's ongoing Lean inference/executor goal. Luna owns dispatch, isolated primary verification, review assignment, integration and Git.
Branch: `research/simple-sub-intrusion`
Baseline: `82b601fe852da2bb4406783ef5cb96ea0d22ae7d`

## Fixed outcome

Construct `YulangClosure.PaperTypes.PaperTupleSplitExecution` as a constructive Lean bridge from the paper's tuple-split reduction to the accepted execution typing and finite ordinary let-control results. Define a simultaneous tuple substitution whose index order matches `extendTupleEnvironment types Γ = types.reverse ++ Γ`; prove the actual split operator returns the simultaneous substitution result at matching arity and preserves the body result type and unchanged `D`, `Xi`, and `Γ`. Extend the existing partial R35 principal step and finite R36 let-stack control conservatively with tuple split, proving successful transition typing preservation and erasure correspondence under every stored let frame.

Do not edit the accepted syntax, R28 term substitution, R35 core step, R36 core control, root imports, tests, fixtures or expected outputs in the proof worker lane. Luna may add only the new module import to the root in an isolated primary checkout after the candidate is frozen, then verify the full target before fresh independent review. The R39 input-port question and whole-state/current-port/residual-graph theorem are expressly out of scope; do not infer or use their authority.

Implementation lane: `NO_SAFE_CODE_SLICE`. `program.rs`'s name/wildcard CasePattern and `machine.rs`'s ReceivedValue/dispatch state do not yet have an approved bridge to this paper binder substitution. Do not change Rust semantics.

This packet can establish only ordinary tuple split within the supported paper execution syntax and finite let contexts. Other split patterns, handlers, mapop, full raw-state preservation, native simulation, inference A/B, whole executor, and production remain OPEN.

## Frozen inputs

- Baseline commit: `82b601fe852da2bb4406783ef5cb96ea0d22ae7d`.
- Manuscript: `docs/yulang-operational-type-safety-ja.tex`, SHA-256 `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`; governing rules are syntax/typing `:229`, split reduction `:308`, and context/preservation scope `:1012–1026,1860–1877`.
- `PaperTermSubstitution.lean` SHA-256 `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`.
- `PaperCoreStep.lean` SHA-256 `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
- `PaperCoreControl.lean` SHA-256 `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`.
- `PaperExecutionSyntax.lean` SHA-256 `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- `PaperExecutionTypingSubstitution.lean` SHA-256 `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`.
- Current root `YulangClosure.lean` SHA-256 `b4b04a6a3b2cc0c7c330e93195539f7344612347c9b51b7f2dc8cf0be4994454`; it already imports R43's integer-comparison module.
- Lean toolchain `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`; lakefile `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`; manifest `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`.
- Supporting accepted handoffs: R28 `tasks/agent-loop/inbox/paper-typing-subst-r28.md`; R35/r3 `tasks/agent-loop/inbox/paper-core-step-r35-r3.md`; R36/r2 `tasks/agent-loop/inbox/paper-core-control-r36-r2.md`. Reconfirm their contents against these frozen source hashes; handoffs are navigation/evidence, not additional authority.

## Required construction and falsifiers

1. Define a total replacement vector over the tuple's component values and an outer replacement `ρ`. Binder index zero selects the last ordered tuple component, because the body environment is `types.reverse ++ Γ`; indices past tuple arity map to the correspondingly decremented outer `ρ`. Apply the existing simultaneous `termSubstituteComputation`; do not implement repeated/sequential single substitution.
2. Prove the vector is `TermSubstitutionTyped` from `extendTupleEnvironment types Γ` to `Γ` using `ValuesTyped` and identity typing for the tail. Prove exact list/value/type arity needed by the split rule; retain the `binders.length = types.length` premise and require runtime tuple/value arity match before reducing.
3. Define an executable split redex result for `.split (.tuple values) binders body`; all other values and arity mismatch return `none`. Establish exact correspondence between the operator output and the simultaneous replacement, and `PaperComputationTyped` preservation for arbitrary shared `D`, graph environment, outer environment and result type.
4. Extend R35's partial principal operator without editing it. Prove every `some` result preserves typing: the R35 cases use the accepted R35 theorem; split uses the new theorem. No completeness claim for unsupported forms.
5. Extend R36's ordinary let control in a new operator/relation, keeping its push/pop/delegate priority and stored frame order. Prove `StateTyped` preservation and erasure stutter-or-one-step under all finite let frames. Preserve one final result type and unchanged shared contexts.
6. Include checked falsifiers/examples for: heterogeneous two-component tuple order; empty tuple; external variable beneath at least one binder; arity mismatch; and a case distinguishing simultaneous replacement from sequential replacement. Examples do not replace universal theorems.

No `sorry`, `admit`, `axiom`, unsafe checker bypass, new premises, weakened quantifiers, altered old theorem, or expected-output change. Report any unavoidable source/model mismatch as a blocker rather than guessing semantics.

## Lanes, exact outputs and resource gates

### Proof worker

One registered `lean_prover`, child agents forbidden. Fresh detached checkout `/tmp/yulang-r44-tuple-split-prover` at the baseline; its dedicated `.lake/build` is worker-only. Exact write lease: new `notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean`, `.lake/R44Audit.lean`, `tasks/agent-loop/inbox/paper-tuple-split-r44.md`, and complete command/stdout/stderr receipt `tasks/agent-loop/inbox/paper-tuple-split-r44-worker.log`. No root file, accepted source, test, Git or other path writes. Worker grant: 1200 active seconds, at most 10 literal Lean/Lake invocations, at most 120 cumulative checker seconds and 60 seconds per call. Include pinned Lake and Lean version queries in the call count. Stop on first checker failure, timeout, pin mismatch, or cap; no diagnostic retry beyond remaining authorized calls.

Required theorem audit covers every public theorem in the new module: full declaration kind/type, complete `#print axioms`, and `Lean.collectAxioms` audit restricted to `{propext, Quot.sound}`. Audit source and complete raw logs are written before handoff. No claim of parent closure from a proposition definition or test/example.

### Luna primary

After worker cessation, independently verify hashes and source boundaries in a separate detached checkout `/tmp/yulang-r44-tuple-split-primary` at the exact baseline; copy only the hash-matched module and audit source. Add one import to the isolated root after the source audit is frozen. Four primary Lean/Lake calls maximum, 60 cumulative checker seconds: pinned Lake version; pinned Lean version; default root target build with the new import; complete audit execution. Capture exact command/cwd/exit/duration and full raw output from process launch; stop on first failure or cap. No Lean calls in the main worktree.

Fresh independent `compiler_referee` after primary freeze: inspect the exact new module, all theorem declarations and audit, full logs, isolated root import/build, all frozen dependency pins, the falsifiers and source/spec boundaries. Reviewer checker/build/test/Git calls are forbidden; max 180 seconds, conservatively charge full if unknown. Any blocking/major finding stops integration.

Only after CLEAN review may Luna copy byte-identical module and isolated root into the main worktree, update current state, run the prescribed sprint tooling check, and commit/push explicit paths. No change to other modules or pending questions. Do not run additional Lean in the main worktree.

### Integration gates

Success requires all exact source pins, a constructive simultaneous replacement respecting reversed environment order, arity and capture falsifiers, all public theorem types and strict axiom audits, successful isolated default root build, fresh CLEAN review, exact-byte primary integration and review/verification receipt hashes. An open R39 question, other split-pattern execution, full state theorem or implementation gap remains explicitly OPEN.
