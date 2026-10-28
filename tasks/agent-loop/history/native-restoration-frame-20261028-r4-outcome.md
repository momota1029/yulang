# NATIVE-RESTORATION-FRAME/r4 outcome

Status: **CLOSED_INCOMPLETE**. No Cargo, Lean/Lake, test, build, or formatter
checks ran. Parent theorem, source/native correspondence, prepared-root
preservation, FreshUse coverage, effect hygiene, and production gates remain
OPEN.

## Frozen inputs and outputs

- Contract: `tasks/agent-loop/sprints/native-restoration-frame-20261028-r4.md`
  SHA-256 `0c76993f4759bef5ff466fd039ce5d551fcec10996ab6d6c40f6643a5af87902`.
- Baseline: `2c63118937324500a41582f1c452117b819396f7`.
- Rust `candidate_scheme.rs`: SHA-256
  `2573e66766f54bae5f10a9f645976b16c27b770d4db0c2f0fe3be76eb26906af`.
- Rust `candidate_extrusion.rs`: SHA-256
  `85f45d14b88ca777b94abcaa254983e5bd7e72d6d452aa226c002c3c541fc50d`.
- Rust handoff: `tasks/agent-loop/inbox/native-restoration-frame-r4-rust.md`
  SHA-256 `342bfb04825a1443fb6383cd18d44b215d8ecf956190043a69209d03ca1df7bd`.
- Lean candidate:
  `notes/theory/lean/YulangClosure/NativeRestorationFrameR4.lean` SHA-256
  `b2c185413cf537b22a91c04c97bdd5c30ce0f44afe83c91cbbc2eff1e32708f0`.
- Proof handoff: `tasks/agent-loop/inbox/native-restoration-frame-r4-proof.md`
  SHA-256 `a33d0cccf7bff422e5f8ad050f30e0243f6d86ebf7eeba642e1b2be0bf9b7334`.

The proof handoff reports 21 constructed candidate lemmas for local identity and
physical frames, sequence induction, computed emission lookup, and modeled
completed readback. They are **unchecked**: no Lean execution, printed theorem
types, or axiom audits were produced. The first source-to-Lean gap is
`candidate_context_step_replay_child`, `ReplayChildWait::Idle` with an item,
calling `start_typed_drain`, followed by nonterminal Transport/Context/Dispatch
children. No theorem authenticates that transition sequence or the saved
restoration control. The proof worker reported approximately 761 of 1,200
seconds used; serving model/effort and exact process measurements remain
UNKNOWN.

## Independent review

The source-first Rust review returned **REJECT**. Findings:

1. **BLOCKING:** `candidate_extrusion.rs:1055` applies `?` to an `Option` in a
   `Result`-returning function, preventing the test configuration from
   compiling.
2. **BLOCKING:** the observer is recorded only by
   `candidate_restore_bound_with_evidence`, while source execution calls
   `begin_candidate_fresh_bound` and directly drives restoration. The test
   invocation vector therefore remains empty and its nonempty assertion fails.
3. **BLOCKING:** FreshUse readback compares the mapped relation against the
   captured source bound, although native reconstruction maps it to the
   destination bound and records a source-to-destination dependency. A valid
   fresh copy can have different endpoints.
4. **Major:** raw transformer readback checks only that the transformer ID
   resolves. It retains no expected raw transformer witness, so replacing the
   raw row under the same ID is not detected.

The reviewer also found the `RowKey × BoundLane` match exhaustive and the
mutation borrow boundaries short. No checks or writes were performed by the
reviewer. Because any rejection closes this contract incomplete, no Rust
revision or check was authorized.

The reviewer did not inspect the frozen Lean artifact: it could not authenticate
at least 120 seconds remaining in its original 700-second grant. It made no
Lean acceptance claim. The Rust rejection remains terminal.

## Disposition

The R4 Rust and proof workers froze their handoffs and stopped. No source,
compiler, test, Lean, or build checks ran. Parent and production gates remain
OPEN. The next packet must authenticate the actual source invocation boundary,
destination relation plus transport dependency for FreshUse, raw transformer
content, and every successful native child branch before claiming completed
readback. The first currently identified missing proof branch is
`ReplayChildWait::Idle → start_typed_drain`.
