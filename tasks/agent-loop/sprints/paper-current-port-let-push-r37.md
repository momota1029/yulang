# Sprint PAPER-CURRENT-PORT-LET-PUSH-20261026/r37 — source/control intake

Status: READY; Luna-only source investigation. No worker or checker admission.
Branch: `research/simple-sub-intrusion`
Baseline: `858eb47b0` (R36/r2 bounded result integrated after CLEAN source review)
Selector boundary: R36 sprint end; selector recommends one let-push source/control correspondence packet.

## Fixed outcome

Investigate exactly one original-parent case: ordinary `let` active-child descent /
R36 let-push. Determine whether the manuscript's full-state judgment and
current-port invariant provide an actual projection to the R36 state
`⟨head, stack⟩` for this transition. Record, with primary-source locators:

1. the full-state evidence used before and after the let-push;
2. the exact active computation and finite pending-let frames represented by
   R36's `head` and `stack`, including frame order;
3. whether the same derivation graph, joint assignment `η`, and port table `U`
   are retained across this case;
4. the next active code label/input port, and the source premise that establishes
   its concrete diagram membership; and
5. the first missing definition or proof obligation, with its owner and a
   discriminating falsifier, if any of these cannot be established.

This is source/control correspondence research, not a Lean theorem or a claim of
the original parent. Do not infer current-port membership from erasure equality,
choose a different `η` per port, narrow formal seeds, use an old heap activity
snapshot as current evidence, or import `CoreControlBridge`'s separate grammar.
Retain the manuscript's requirement for the same typed derivation graph/residual
or declared latent/reentry instance, value type, current-port concrete diagram
inclusion, immutable fresh graph extension, and uniform binder renaming.

## Governing sources and frozen dependencies

- Manuscript `docs/yulang-operational-type-safety-ja.tex`, SHA-256
  `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`;
  authority locators: active-child and ordinary reduction `:305–334`, finite
  Horn closure and shared `η` `:1544–1559`, full current-state evidence and
  one-step parent `:1845–1866`, closing case analysis/active-child induction
  `:1867–1907`.
- R36/r2 `PaperCoreControl.lean`, SHA-256
  `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`.
- R36/r2 contract, SHA-256 `84c679419e1fd4cb75f4d16e2c2b9c537f0f10e5b29ac6d5fe885e697079bfe2`.
- R36/r2 handoff, SHA-256 `bc4046485dccea2750f1e24b91696ba0ba2c0fe52fc05bbf5bce3e8e0fcffeac`.
- `PaperExecutionSyntax.lean`, SHA-256
  `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`.
- R35 `PaperCoreStep.lean`, SHA-256
  `503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.

## Scope and resources

Luna owns the only write leases: this contract, `current.json`, and
`tasks/agent-loop/inbox/paper-current-port-let-push-r37.md`. All source/dependency
files are read-only. No agents, descendants, Lean/Lake/checker, cache, build,
tests, Rust, implementation, fixture/diagnostic/expected-output or semantic
changes.

New R37 grant: at most 600 Luna active seconds, zero native/checker invocations,
zero workers, no Astra, no carryover/reset from R36. If the exact source evidence
cannot establish a projection or the remaining time cannot be established, stop
with the first missing premise/owner. A later independent review or Lean packet
requires a separate selector decision and exact grant.

Before: R36 establishes only paper-syntax ordinary let state preservation and
stuttering simulation for finite let frames; the full-state/current-port bridge
is unproved. After: one let-push source/control mapping is either evidenced at
all five listed points or reduced to a precise source definition/proof gap.
The original parent, other frames, source/native, inference A/B, and production
remain OPEN. `NO_SAFE_CODE_SLICE` after inspecting the relevant owners
`PaperCoreControl.lean` and `PaperExecutionSyntax.lean`.
