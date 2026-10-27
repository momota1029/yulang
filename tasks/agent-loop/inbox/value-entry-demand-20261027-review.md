# VALUE-ENTRY-DEMAND-20261027 — independent frozen review receipt r1

Reviewer: `/root/value_entry_review`, fresh non-author reviewer. Actual launch and active read-only review acknowledged in this session. Observed model and effort: **UNKNOWN**. No descendants, checker processes, generated outputs, file edits or Git mutations.

Disposition: **ACCEPT as conditional lemmas about a post-Delay-allocation machine projection and a definitional receipt-size mismatch.** This does not establish complete native entry provenance, source admission-to-demand correspondence, `EntryFacts`, or original parent closure.

No BLOCKING or major correctness findings against that restricted interpretation. One minor scope-reporting finding appears below.

## Frozen evidence

Verified actual workspace SHA-256 values:

| Artifact | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/OriginalValueEntryDemand.lean` | `9a171ecfbad7d632b2a15ef1f57d2d2dd46444aa36452de9158f1d1c7cfdae63` |
| `notes/theory/lean/AuditOriginalValueEntryDemand.lean` | `efceba608e3942710c4f53d8bfc1516ba3f18c5470b7fae64810e04020d04772` |
| `tasks/agent-loop/inbox/value-entry-demand-20261027.md` | `63abf6e04d1d8d6b365690ff0bbf345978b56a08f2f6903fe9fd322e9139267f` |

The contract is `tasks/agent-loop/sprints/value-entry-demand-20261027-r1.md`. Initial semantic assessment used the contract, actual Lean declarations and Rust owners before reading the author's explanation.

Read governing authority and original-scope material, including the top-level inference principles, original intrusion preservation statement and birth-level SCC correction. Consulted actual direct owners include `OriginalFormalShared`, `OriginalRecursivePair`, `OriginalParameterWorld.nativeEvidence`, `OriginalIdentityRealization.receipt_recovers_call/ForceCut`, `OriginalIdentityCarrier.EntryFacts`, `OriginalReturnWorld`, and the prior independent review.

I ran no checker. The primary's preserved target-build log reports successful completion of 28 jobs; its hash matches `f45e4cb5fe60f2659c219214a63726b2b99aac54f0eb10d7e64d066d20f060aa`. The preserved audit log hash matches `55cc202962dee5cc60f6d01146317024cc9f4d005ab398357a1e917227c4776c`. Independently counting its markers gives 238 beginning/end pairs, agreeing with its census of 238 declarations and 58 theorems. These include generated declarations; they are not 58 authored theorem roots.

The observed nonempty axiom sets are exactly `[propext]` and `[propext, Quot.sound]`. `source_call_recovery` has the latter set. The audit enumerates target-originating constants, prints their types and transitive axioms, and rejects project axioms and dependencies outside its standard allowlist. No checker-bypass mechanism appears in the candidate or audit. These are credible checker receipts, distinct from source correspondence.

## Adversarial assessment

**1. The model captures a useful suffix, without proving its native realization.**

`OriginalValueEntryDemand.lean:113` begins with a lookup of an already installed Closure and an independently supplied argument handle. Rust's corresponding Closure branch starts at `machine.rs:1224`. From there, the represented successful Value path has the correct order:

- allocate the invocation and change current owner;
- substitute the Closure's captured environment using receiver dispatch;
- push ReceiverReturn, then ValueEntry;
- execute the argument Delay using substitution `None`;
- evaluate its code in the Delay's own saved environment.

The innermost-first Lean list correctly reverses Rust's frame-vector presentation. The full source `Parameter` retains formal, pattern and body data. This is a manually defined projection; there is no Rust-state encoding, source-code-label law, or simulation theorem establishing that arbitrary Lean inputs describe a real Rust state.

The change exposes the missing owning correspondence law. It does not repair that law or discharge native provenance by itself.

**2. Receiving mutations need the precise starting boundary.**

Rust `Frame::Callee` allocates the Delay value and calls `receiving.delay` at `machine.rs:1188–1198`, before Closure lookup and invocation allocation. `receiving.rs:245` defines `delay` by appending a new view with the inherited image/unknown coverage. The candidate does not construct either allocation.

Starting **after** those operations, the represented Closure Value suffix performs no receiving mutation before `execute` opens the Delay. `receiving.enter` and the associated formal receipt belong to the Computation branch at `machine.rs:1300–1311`. `callback_entry` belongs to later ValueEntry processing at `machine.rs:1438–1465`, after the argument Force returns. Neither supplies a pre-Force Value receipt.

Thus unchanged receiving state is correct for the chosen suffix, and incorrect as a description of the entire Callee transition.

**3. Dictionary and failure state are handled honestly within that boundary.**

`substitute`, at line 80, retains the dictionary operation's poststate on either outcome. On dictionary failure, invocation allocation/current-owner change remain, and no new frames have been pushed. This matches the order of `new_invocation` followed by `substitute_environment` and then frame pushes.

Successful composition appends an environment with the old captured environment as parent, no binder, preserved context and composed substitution. The dictionary engine itself remains an unproved operation interface.

The Closure environment and Delay environment remain distinct. `substitute_none` establishes the latter's early exit even with dictionaries enabled. No validity or lookup of that saved environment is asserted merely by opening it.

`invalidEnvironment` correctly identifies a projection boundary corresponding to Rust's direct indexing panic, rather than a native error result. `outsideProjection` likewise marks omitted cases. Request execution, Comp entry and other executable branches are not covered. The failure lemmas do not establish rollback or arbitrary whole-machine poststate correspondence.

**4. Retaining `CallInput` does not connect it to execution.**

`Request`, at line 132, stores the complete `CallInput` and Received records. `Request.run` passes only `argument.value` into the projection; `request_keeps_full_call` is a structural preservation equality. No theorem authenticates its argument view, root, source/provider sites, receiver, or semantic Call fields against native constructors.

This is candidly separate bookkeeping, not the missing admission-to-demand bridge.

**5. Descriptor and source-admission theorems stay within their actual conclusions.**

`selected_return_constructor` applies the existing `nativeEvidence/native_evidence_object` constructor. It proves the supplied source-selected descriptor and assignment projections occur in that retained evidence object. It proves no Return execution, successful Force, Name descriptor alignment, or source-selected/native readout equality.

`source_call_recovery` directly reuses `receipt_recovers_call`. It recovers source admission and its checked challenge/input, preserving the descriptor assignment. It supplies no native receiver, Delay allocation, demand event, or Force relation.

**6. The receipt mismatch is definitional, not a source-qualified counterexample.**

`source_receipt_not_native_prefix` compares two explicitly chosen projected worlds. One preserves receipt-store size; `OriginalRecursivePair.receiveWorld` appends a receipt. The size inequality follows directly. `actual_value_entry_receipt_gap` substitutes the conditional plain-prefix calculation into that inequality.

This refutes raw equality of those constructors from the same supplied initial world. It does not establish a supported source instance, prove temporal refinement impossible, or refute soundness. The actual Source receipt/admission interpretation remains open. Later callback receipt creation cannot make these earlier raw worlds equal.

## Finding

**minor — Explicitly identify the omitted Delay-allocation boundary in the integration scope.**

Locations: `OriginalValueEntryDemand.lean:44–50`, `:113–125`, `:170–185`; handoff lines 20–38 and 113–120. Actual omitted constructors: `machine.rs:1188–1198`, `receiving.rs:245–261`.

Risk: “pre-Force native prefix” or “failure-prefix mutations” can be read as covering the entire Callee transition, although Delay/value allocation and `receiving.delay` already occurred before this model starts. For example, a Closure dictionary failure retains the previously allocated Delay and appended view in Rust; those mutations are absent when comparing this model against a state before Callee processing.

Governing requirement: contract step 2 requires actual mutation ownership and preservation of argument/view provenance; the repository proof-closure contract forbids promoting a missing constructor bridge through an auxiliary model.

Minimum closure for this checkpoint: explicitly record **post-Delay-allocation suffix projection** and the unconstructed Delay/view provenance in the primary outcome/status. No frozen proof edit is necessary for that restricted acceptance. A later claim of complete native provenance requires the actual Delay/value/view constructors and their state correspondence.

## Preserved boundaries and stop receipt

The first unfilled parent premise remains a constructor-respecting interpretation from original source Call/receipt admission to the actual native Value-entry demand. Delay/view allocation provenance, frontend/provider association, dictionary realization and decorated Event readout remain open. The previous Return-assignment versus `native.fields` equation, followed by witness/scope/authority/incidence/dictionary joins, is unchanged and unresolved.

Original A/B quantifiers, all supported source forms, lawful histories, original scopes and the single shared witness remain unchanged. Whole-language soundness, Effect hygiene, principality, progress/termination, source/native correspondence and production remain **OPEN**.

**Rust disposition: NO_SAFE_CODE_SLICE.**

Review complete; no writes were made. The primary owns persisting this receipt, adjudicating the minor finding and integrating only the restricted result.
