# Sprint PAPER-TUPLE-SPLIT-REPAIR-20261026/r45

Status: READY; Luna authorizes this bounded repair inside the user's ongoing Lean inference/executor goal. R44 remains FAILED. No R44 checker grant or result is carried forward.
Branch: `research/simple-sub-intrusion`
Baseline: `7a2e033a703854a6a9fd6011d1cb4896783a1f24`

## Fixed outcome

Repair the single first-build failure in the frozen R44 candidate, then certify the unchanged bounded tuple-split result only if the full worker build and all 27 theorem audits pass. The only permitted candidate edit is the nil branch of `prefixReplacement_tail`:

```lean
| nil => simp only [List.length_nil, Nat.zero_add, prefixReplacement]
```

Seed candidate SHA-256: `17a5f6f6fb4c6f53031c0a28ab0fafed136a78bd84497c5860293d1a329e255c`. The R44 failed candidate, audit draft, complete log, handoff, and FAILED result remain immutable at their R44 evidence paths. R44's 3 calls and 34.055307259 checker seconds are consumed and cannot be refunded or reused.

If the single allowed edit yields any further build or audit failure, stop immediately. No additional repair is authorized by this packet. Keep the original split preservation, simultaneous replacement, reversed tuple binder order, arbitrary shared `D`, graph/environment, outer context and result type, R35 conservative extension, R36 finite let control/erasure, and all five falsifiers unchanged. Do not infer R39 input-port authority or full-state closure.

Implementation lane remains `NO_SAFE_CODE_SLICE`; do not change Rust semantics.

## Frozen inputs

Baseline commit above; original sources/configuration are pinned by R44 handoff `tasks/agent-loop/inbox/paper-tuple-split-r44.md` SHA-256 `b7b03d7bc9ff4e42a442903e8808011e7d285263155bd3074e49c20dc96fd911`. Reconfirm exact bytes before work:

- manuscript `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `PaperTermSubstitution.lean`: `a4f87f9604c03beefdc44de5d45fcd9f5924ca9580c75edf353cf267e69a0d4f`
- `PaperCoreStep.lean`: `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`
- `PaperCoreControl.lean`: `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`
- `PaperExecutionSyntax.lean`: `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`
- `PaperExecutionTypingSubstitution.lean`: `3b1588bff2d28a3db7aa241c930495b84f090e880ad49ac8fb2d593d54943d41`
- baseline root `YulangClosure.lean`: `b4b04a6a3b2cc0c7c330e93195539f7344612347c9b51b7f2dc8cf0be4994454`
- `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
- `lakefile.toml`: `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194`
- `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`

Use the corrected R28 handoff path in the R44 handoff: `tasks/agent-loop/inbox/paper-term-substitution-r28.md`. Supporting handoffs are navigation/evidence; the pinned sources and manuscript are authority.

## Proof worker lane

One registered `lean_prover`, no descendants, no Astra. Fresh detached baseline checkout `/tmp/yulang-r45-tuple-split-prover`, with dedicated `.lake/build` owned only by this worker. Seed the candidate from the frozen R44 inbox artifact, install it at `notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean`, and apply only the fixed nil-branch edit above. Copy the frozen audit draft byte-for-byte as `.lake/R45Audit.lean`; its import path and 27 theorem targets stay unchanged. Do not weaken or rewrite the audit.

Exact output leases in that checkout:

- `notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean`
- `notes/theory/lean/.lake/R45Audit.lean`
- `tasks/agent-loop/inbox/paper-tuple-split-r45.md`
- `tasks/agent-loop/inbox/paper-tuple-split-r45-worker.log`
- dedicated `notes/theory/lean/.lake/build`

No root file, accepted source, test, fixture, expected output, Git, network, Rust, or other task/state path writes. Capture full raw stdout/stderr, command, cwd, exit and monotonic duration at process launch; verify before/after input pins. Literal call budget **4 total**, including Lake and Lean version queries; checker wall **90 seconds total**, **60 seconds per call**; active grant **600 seconds**. Exact sequence: Lake version; Lean version; focused no-cache module build; strict complete audit. Stop on first failure, timeout, pin mismatch or cap. No retry or repair.

Strict audit every public declaration in the module (27 expected): declaration kind, full type, complete `#print axioms`, and `Lean.collectAxioms` limited to `{propext, Quot.sound}`. Audit is not run if focused build fails. Include all five required examples. No `sorry`, `admit`, project `axiom`, unsafe/native bypass, weakened premise, or changed old theorem.

## Luna primary and independent review

After worker cessation, use separate detached checkout `/tmp/yulang-r45-tuple-split-primary` at the exact baseline. Verify frozen hashes and that the candidate differs from the R44 seed only at the one allowed line. Copy only the hash-matched R45 module and audit source; add a single import to the isolated root. Four native Lean/Lake calls maximum, 90 checker seconds total, 60 per call: Lake version, Lean version, default root target build with import, complete strict audit. Capture complete raw output, cwd, exit, duration and pre/post hashes. Stop at first failure or cap. No Lean in the main worktree.

Fresh independent `compiler_referee` after primary evidence freeze, max 180 active seconds, zero checker/build/test/Git calls. It reviews the exact candidate/audit/root delta/logs, all source pins, the one permitted repair, falsifiers and source/spec boundaries. Any blocking/major finding stops integration.

Only after CLEAN review may Luna copy the byte-identical module and isolated root into the main worktree, update current state, run `python3 tools/agent_sprint.py check`, and commit/push explicit paths. Never stage pending question directories. Preserve R44 FAILED permanently.

## Scope boundary

This packet can establish only the paper tuple-split computation and finite ordinary let-control result. Other split patterns, handlers, mapop, full raw-state/current-port/residual-graph preservation, source/native simulation, inference A/B, whole executor, Rust, and production remain OPEN. An audit/build receipt is not full-parent closure.
