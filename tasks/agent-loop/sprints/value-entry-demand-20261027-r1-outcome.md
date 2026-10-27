# VALUE-ENTRY-DEMAND-20261027/r1 — primary outcome

Disposition: **accepted as conditional lemmas about a post-Delay-allocation machine projection and a definitional receipt-size mismatch**. The packet did not construct the complete native Callee-to-Force provenance. No original source/native parent or production gate is closed. Baseline `40e7714c5e46a8ad870b3d07c238837dfc9cba88`; branch `yulang3`.

## Constructed suffix and exact start boundary

`OriginalValueEntryDemand.invoke` models the Closure branch after the argument Delay value/view already exist and Closure lookup has selected the Value-entry Closure. It computes receiver allocation, captured-environment substitution, ReceiverReturn/ValueEntry frame setup and execution of that same Delay. The receiver dispatch and Delay execution substitution are distinct; `execute_same_delay` proves the latter uses `None` and evaluates in the Delay's saved environment.

The represented plain success case retains the whole source `Parameter`, receiver/previous-owner and both captured environments. The abstract dictionary operation keeps its poststate on both success and failure; invocation allocation/current-owner persists if captured-environment substitution fails before frames are pushed. `Request` stores the complete `CallInput` but does not connect its fields to native handles or an admitted source challenge. `selected_return_constructor` uses the existing selected descriptor in `nativeEvidence`; it does not prove that a Return executes or aligns a later native Name observation.

**Start boundary:** Rust `Frame::Callee` first allocates the Delay value and calls `receiving.delay`, which appends a view carrying inherited image/unknown coverage, before Closure lookup and invocation allocation (`machine.rs:1188–1198`, `receiving.rs:208–222`). The Lean candidate does not construct those operations or prove their operands match its Delay/view inputs. It starts at the post-Delay-allocation suffix. `receiving.enter` plus formal receipt belongs to Computation entry. Rust `callback_entry` mints the Value callback receipt only after Force returns and the ValueEntry frame executes (`machine.rs:1438–1465`, `receiving.rs:300–335`); it is not a pre-Force source receipt.

The reviewer’s minor scope-reporting finding is closed here by naming the restricted post-Delay-allocation suffix and leaving Delay/value/view provenance OPEN. No frozen Lean source was changed.

## Receipt-size obstruction and parent application

`source_receipt_not_native_prefix` compares the Lean suffix's unchanged receiving store with `OriginalRecursivePair.receiveWorld`, which adds a source receipt before Force. `actual_value_entry_receipt_gap` applies the computed suffix result. This proves those chosen raw worlds are not equal. The suffix is a manually defined projection with no Rust-state encoding or simulation theorem, so this is not a source-qualified counterexample, a soundness refutation, or proof that every valid abstraction fails.

`source_call_recovery` reuses `receipt_recovers_call` only for source admission and its checked challenge/input; it supplies no native receiver, Delay allocation, demand event or Force relation. The first unfilled parent premise remains a constructor-respecting interpretation from original source Call/receipt admission to the actual native Value-entry demand, including Delay/view allocation provenance and frontend/provider association. The previous Return-assignment versus `Native.fields` equation and subsequent decorated-event fields remain OPEN.

Original A/B quantifiers, source domain, lawful histories, scopes and shared witness are unchanged. Whole-language soundness, Effect hygiene, principality, progress/termination, source/native correspondence and production remain OPEN.

## Verification and review

The proof worker exhausted six calls/54.166470 seconds. Its final artifact was explicitly **constructed but unchecked**: the intermediate build passed; final root checks failed before type/axiom reporting; the last call targeted an unregistered standalone audit module. All failures remain in the frozen handoff. The worker claimed no final theorem or axiom results.

Primary verification on a separate isolated project copy used pinned Lean 4.35.0:

- `lake build +YulangClosure.OriginalValueEntryDemand`: exit 0, 28 jobs.
- `lake env lean -j1 -M1024 AuditOriginalValueEntryDemand.lean`: exit 0.

The origin census printed complete types and transitive axioms for 238 originating declarations, including 58 theorems and generated declarations. The only nonempty axiom sets were `[propext]` and `[propext, Quot.sound]`; `source_call_recovery` depends on the latter. The audit rejects project axioms and unapproved transitive axioms. Logs:

```text
primary-target-build.log  f45e4cb5fe60f2659c219214a63726b2b99aac54f0eb10d7e64d066d20f060aa
primary-origin-audit.log  55cc202962dee5cc60f6d01146317024cc9f4d005ab398357a1e917227c4776c
```

Fresh non-author `compiler_referee` review accepted only the restricted conditional interpretation, with no blocking/major findings and one minor scope-reporting finding closed above. Its receipt is `tasks/agent-loop/inbox/value-entry-demand-20261027-review.md`, SHA-256 `6b9b1a67551e679af7c5b82197f2274eb764b02d6dde1f1d1ecfac8655e4276c`. The reviewer ran no checker; primary verification is separate.

Rust disposition: **NO_SAFE_CODE_SLICE**. No Rust or compiler source, root import, source domain, toolchain, manifest, expectation or design authority changed.

## Frozen artifacts and stop state

```text
9a171ecfbad7d632b2a15ef1f57d2d2dd46444aa36452de9158f1d1c7cfdae63  notes/theory/lean/YulangClosure/OriginalValueEntryDemand.lean
efceba608e3942710c4f53d8bfc1516ba3f18c5470b7fae64810e04020d04772  notes/theory/lean/AuditOriginalValueEntryDemand.lean
63abf6e04d1d8d6b365690ff0bbf345978b56a08f2f6903fe9fd322e9139267f  tasks/agent-loop/inbox/value-entry-demand-20261027.md
6b9b1a67551e679af7c5b82197f2274eb764b02d6dde1f1d1ecfac8655e4276c  tasks/agent-loop/inbox/value-entry-demand-20261027-review.md
```

Proof author and reviewer stopped with no descendants; their repository output leases were handed to the primary after cessation. This partial result narrows the source/native Call-entry obligation but closes none of the original whole-language gates.
