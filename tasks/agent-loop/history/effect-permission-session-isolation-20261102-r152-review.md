# R152 independent review — revision 1

Verdict: PASS for checkpointing the exact unapplied research candidate only. No BLOCKING, major or minor compiler-correctness finding established in this review. No production integration, parent-theorem closure or executable correctness certification follows.

Sprint: EFFECT-PERMISSION-SESSION-ISOLATION/20261102-R152.
Contract revision 1: tasks/agent-loop/sprints/effect-permission-session-isolation-r152.md.
Contract SHA-256: 5fd4a9441a90be2b1201b179d8afb83c71ca2bbf4a8ca25c6f78e4da0d5bcc51.
Reviewer: /root/r152_independent_review; no descendants.
Assignment: fresh independent compiler_referee; requested model/effort gpt-6.1-sol/medium, observed model/effort UNKNOWN/UNKNOWN.
Baseline: 225c5519943fc490c3d5620683918674f4f6afd5.

## Evidence and isolation

I read the candidate and governing authority, then inspected committed baseline constructors, direct dependencies, retained mappings, export checks and relevant test bodies before reading the two author handoffs. Author explanations were not evidence for the initial analysis. All Rust reads used committed blobs; no dirty Rust source, candidate_receiver.rs or quarantined runtime file was inspected.

Authenticated inputs:
- Candidate patch: 3a5a2f73b75cd3caaecae7fbb0f36c60b9c33492502fe531f3e7237fdb9838c4.
- Source handoff: a18dc477d33e639b002cd22d4825e56640c7ab6c25b0a1f4eebc61974c58094c.
- Proof handoff: ac040d9ad233fce3ac29b9e5fe3b092261d30a7003bf41238f96e151fe9c0b39.
- Frozen input patch: 643d75e8e8435253a8606af7800134c28ce8eb74c86b1880ab169d5b8891bd1a.

Independently recomputed committed Rust SHA-256:
- candidate_effect.rs: 102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01.
- candidate_scheme.rs: e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814.
- shadow_apply.rs: 2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278.
- candidate_context.rs: a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905.
- candidate_call.rs: fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f.
- lib.rs: 429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be.

Governing clauses: annotation-effect-hygiene integration §§1.1–1.2, 3–4; inference top-level principles §§3–5; design-authority natural-behavior and source-owner requirements; R152 full-candidate and unapplied-only boundary.

## Cause, ownership and deleted checks

The candidate repairs the argument-ownership cause. Its scheme binder has the baseline single-session signature and obtains route, native arena, batch registrations, context origins and permission state from that one session. A caller cannot supply A's route and B's permission state through this entry point. A shared borrow lifetime or equality of source IDs is not being substituted for session identity.

At baseline candidate_scheme.rs:499–581, preserved checks authenticate the unique registration-labeled context origin, exact Lambda occurrence, original Function's negative Effect live variable, unique source Lambda recipe, HIR Lambda and parameter identity, current canonical representative and mapped native argument-effect ordinal. Candidate patch lines 1451–1469 retain these checks while adding raw-entry agreement with the retained incidence. The lower State binder at baseline candidate_effect.rs:397–440 retains registration, owner, scope, parameter, occurrence, raw entry and nonempty concrete payload checks. Its independently supplied low-level arguments remain an internal precondition; the committed Rust caller search found only the scheme wrapper calling it.

The removed provider-equals-constructor-owner guard is justified for this adapter's meaning. Baseline lib.rs:11621–11774 constructs the actual Function and records registration, Lambda and raw entry together. Capture at candidate_scheme.rs:2957–2989 selects that exact Function endpoint, follows child 1 and checks its canonical Effect row. FreshUse at :4529–4559 preserves this registration-labeled incidence through the shared row map. Thus a returned/local Function can retain its actual constructor registration when a different module definition supplies its value. Source authentication still follows that registration into its own source HIR. Restoring unconditional provider equality would reject this legitimate ownership distinction. No replacement handler/provider/Catch-arm authority is inferred from the returned permission record.

The new raw entry is copied through Capture, FreshUse and native incidence; it does not replace either the captured representative or mapped row. Existing sizeof-based accounting covers the larger incidence records. The native incidence type visibility change exposes no new public compiler API and adds no producer or consumer.

## Other candidate changes and failure paths

The remaining candidate changes are test instrumentation and test bodies. Typed constructor, source site, memo, delegated port, canonical intern, captured-row and capture-owner observations are cfg(test). They do not introduce handler subtraction, permission creation, solver decisions or production publication. The non-test tail-row local binding returns the same value as the prior call. Observer allocations and thread-local retained IDs are test evidence only, not a solver owner brand or a proof of cross-session isolation.

The original tuple permission, distinct-port, residual and transaction-restoration assertions remain in the original test; additional helper fixtures do not replace those expectations. The separate unequal-transport probe remains an unexecuted assertion, not evidence that unequal transport was observed. The named-result-function probe exercises capture/export APIs but does not establish handler execution or complete returned/local coverage.

The binder returns None on absent or inconsistent provenance and performs no solver mutation. Capture/FreshUse changes add retained scalar provenance inside existing fallible construction and publication boundaries. Export at baseline shadow_apply.rs:2681–2718 still rejects the entire permission projection on a missing path/domain/row; the added export trace does not publish a partial permission list. No rollback owner or restoration logic is deleted by this candidate.

## Remaining gates and minimum next evidence

No repair is required to checkpoint this exact candidate as an unapplied research artifact. Before any wider integration, the primary must independently disposition the excluded receiver changes and establish actual consumer/provider/arm authority at their owner. This review supplies no verdict on excluded files.

R152's single-session API repair is supported by static source ownership. Whole source/native correspondence, INITIAL-STATE, CONSUMER, soundness, principality, termination and original A/B obligations remain OPEN. Concrete returned/local source coverage, compilation and test results remain unestablished. The proof handoff's conditional falsifier concerns the frozen input API and is not an executed counterexample; the candidate removes that argument-joining interface.

## Resources, output and stop

Budget: at most 360 seconds; no descendants. Exact wall elapsed is unmeasured. Builds, tests, Lean, scratch/cache/environment creation, checkout/worktree and Git mutations: zero. Read-only Git object inspection and hashing only.

The higher-priority read-only instruction prevents writing the leased review path. This exact body is returned for the primary to freeze at tasks/agent-loop/history/effect-permission-session-isolation-20261102-r152-review.md. No filesystem output was written. Reviewer STOPPED after this frozen receipt; no pending descendant or write lease remains in use.
