# R15 proof repair — frozen rev1

Sprint: `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r15`. Producer: `/root/effect_permission_term_call_control_r15_lean`, registered `lean_prover` leaf. Constructed-but-unchecked; primary owns the isolated build/cache, the complete 38-root audit and subsequent independent review. No descendants.

## Frozen inputs and source scope

- Contract: `tasks/agent-loop/sprints/effect-permission-term-call-control-20261029-r15.md`, recorded SHA-256 `eff6b4718b194b07e807db84872926565448b4baa86ae2fd02d3b052fcfcfc50`.
- R15 source handoff: `tasks/agent-loop/inbox/effect-permission-term-call-control-r15-source.md`, recorded SHA-256 `7500b0fe883f354387ed9298e2f7aa5b125bb8b89256769b5da3f9f9bb64a7ed`.
- R14 archived baseline: `tasks/agent-loop/history/artifacts/FormalPermissionTermCallControl-r14.lean`, measured SHA-256 `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc`.
- Direct import `YulangClosure.FormalPermissionConnectedCuts`: measured SHA-256 `6427eed5f0c3b84f80a3a37c31797fc782960c725fb77f6bef46cebcc993b023`.
- `YulangClosure.FormalPermissionHelperFrames`: measured SHA-256 `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`.
- Rust `crates/yu-solver/src/lib.rs`: measured SHA-256 `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`; `candidate_effect.rs`: `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`; `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.

Read root operating instructions, goal-driven sprint rules, the Lean proof skill and its source/execution references. The original parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1, with source-completeness obligation §5 and the birth-level qualification correction in `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Measured hashes: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` and `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`. The original scope remains every supported source program and lawful finite construction history, with original scopes and shared witnesses; soundness, principal coverage, progress and termination remain separate obligations. Research notes do not grant semantic authority.

For this local repair the relevant exact source is `InferenceSession::with_term_events`, `lib.rs:10594–10621`, and `sample_f4_resources_with_term_snapshot`, `lib.rs:10804–10818`, together with the frozen R14/R15 source handoffs. Actual `HelperState`, `HelperOp`, `applyOp`, `loopState`, `drained`, `controlState` and `testFields` were inspected. Test fields are identities in this candidate production model; the actual Rust cfg(test) writes are excluded from its execution interpretation.

## Exact repair and unchanged declaration

Changed only the proof body of `YulangClosure.FormalPermissionTermCallControl.control_test_fields` in `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean`:

```lean
theorem control_test_fields (constructor : ConstructorOutcome) (events : List EventOutcome)
    (accounting : Bool) (s : HelperState) :
    testFields (controlState constructor events accounting s) = testFields s
```

These are universal parameters; there are no added success, availability or endpoint hypotheses. The false branch retains the existing drain-only simplification. The true branch first changes to the definitionally equal loop-at-drained-state goal, applies `YulangClosure.FormalPermissionTermCallControl.loop_test_fields events (drained constructor events s)`, then proves the drain's instrumentation projection equality using only `[drained, applyOp, testFields]`. It avoids unfolding `testFields` before the loop lemma is applied.

Rev1 artifact SHA-256: `73bface0963c65eb76933ff8116594b161e78f1733b66e6be25cc174d1eb2dd7`.

An actual Python `pathlib`/`hashlib`/`difflib` comparison against the archived baseline exited 0 at `2026-10-29T14:11:17.445709+00:00`. Its three byte comparisons were all `True`: prefix before the declaration unchanged; declaration through its statement unchanged; suffix after this proof unchanged. Consequently every definition/model, hypothesis, other declaration and inherited import stayed byte-identical. Delta: replace one combined branch tactic with nine explicit branch/proof lines. This is a static byte comparison, not a Lean check.

## Failure evidence and verification handoff

Preserved material failure evidence is the original `/tmp/yulang-effect-permission-term-call-control-20261029-r14/attempt-1/stdout.raw` and `audit-receipt.json`, read without modification. That historical audit reports Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; version commands exited 0. Its build exited 1 at `FormalPermissionTermCallControl.lean:231:80`, true-branch goal, after the simplifier expanded the instrumentation tuple and left six loop-field equalities. Its receipt records 14.67 seconds, 798108 KiB maximum RSS and zero printed roots/pass lines. This is historical R14 evidence, not an R15 execution receipt or counterexample.

The current project files were read: `lean-toolchain` pins `leanprover/lean4:v4.35.0`; `lakefile.toml` uses `-j1`, `-M1024`; `lake-manifest.json` has no packages. Per this packet, producer ran **zero** Lean/Lake/checker probes, tests, Cargo or Rust executions. Therefore actual R15 versions/exits, printed theorem types and `#print axioms` results are **NOT_RUN**. The displayed declaration is source text, not checker-printed output. No kernel acceptance, independent review or source/native correspondence is claimed.

Primary next action: freeze/copy exactly the rev1 hash above into its isolated audit input, run the skill checker with the fixed 38-root inventory, and inspect every printed theorem type and complete transitive axiom result. A failed audit returns actual diagnostics to the same repair owner only if its original budget remains; inherited failures or a required statement/model change trigger the contract stop condition.

## Parent application, omissions and cessation

The unchanged `YulangClosure.FormalPermissionTermCallControl.exact_tree_r9_from_term_control` already applies `exact_tree_r9_from_connected` to `sourceCalls inputs initial level`. Its explicit `length`, `Aligned`, `Reservations` and `SourceCalls` parameters remain intact. This repair removes a candidate proof-construction obstruction to checking that module; it establishes no new concrete instance of `SourceProblem.InferenceSoundness`, `SourceScopedCoverage`, `PrincipalCoverage`, `NativeCorrespondence` or `InferenceTermination`.

Represented cases remain both accounting flags, empty/nonempty ordered events, successful sampling, first sampling error with retained partial counter changes, either constructor outcome and the eight generated paired term-call cuts. Omitted evidence remains constructor event generation, sampler availability, actual Rust-to-model execution/state/path linkage, primitive/alias authenticity and native publication. First immediate premise: successful complete 38-root audit, owner Luna; next review owner is primary-assigned fresh nonauthor. First source bridge remains actual Rust execution to explicit constructor/sampler inputs, owner primary source/implementation. Original parent and production gates remain OPEN.

Only the leased Lean artifact and this handoff were written; no scratch/generated outputs, global settings, dependencies, shared records or Git mutations. Resource use: one construction allocation capped at 300 seconds; exact active elapsed/RSS was not instrumented, so no exact total is asserted. Tool-reported shell read/static-comparison calls each completed in 0.1 seconds; no build process ran. **Rev1 frozen; all writes stopped; no descendants; no further artifact edits.**
