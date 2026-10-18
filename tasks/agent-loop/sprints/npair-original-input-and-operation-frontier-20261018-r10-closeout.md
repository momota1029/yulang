# r10 closeout — compile gate failure

Sprint `npair-original-input-and-operation-frontier-20261018-r10`, contract revision 4 (`e9b7bf0bf33f604b8110d891c336ea9a29efce9259a67cee01c80ba0821c67f9`), is **ENDED-PARTIAL-REVIEWED**.

## Parent theorem

`CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains **OPEN**. Original-condition closure: **0**. The authentic historical source/CST/HIR and complete semantic Operation package remain `INPUT_UNAVAILABLE`. Fixed `c`, quantifiers, source domain, R/W/Z, `rho_u`, consumer, F1/FK1, and accepted semantics were not changed. No counterexample or new source/native evidence was established.

## Implementation and verification

Rev4's one named source/native probe was independently code-reviewed **CLEAN** at exact hashes before its sole compile attempt. The exact authorized offline compile-only command ran once and exited **101**. Compiler diagnostic: E0308 at `candidate_effect.rs:2351`; opaque `FactId` was compared to `&ConstraintOccurrenceId`. The direct exact test invocation count is **0** because Cargo produced no test executable. Therefore parser/HIR acceptance, scheduled Operation execution, refusal, root cleanup, and slot-42 behavior remain unobserved.

The complete captured stdout/stderr and compile-only metadata are in the three leased runtime files. The receipt was independently reviewed **CLEAN** for contract conformance. UTC/monotonic compile timing was not captured and is left null; it was not reconstructed. No retry or test expectation change occurred. Static tooling check and `git diff --check` passed; these do not establish compilation.

The source-only test delta remains in the working tree at SHA-256 `22a9e7a25f59638a24df746be9954ec711ca99f7c89802fa75808d7e07fdcca3`, with the known compile failure. It is not an accepted implementation. A successor requires a fresh contract, exact lease, independent review, and a new single verification grant. The local fix target is the slot-42 publication probe: `SemanticFact::id()` is a `FactId`, while source occurrence identity is available through store provenance causes.

## Review and closeout

- Rev4 code review: CLEAN; exact test-only scope, declaration/use identity and source-action trace checked.
- Rev4 failed-build receipt: CLEAN; log hashes/exit/error checked, direct invocation not run.
- Compile gate: BLOCKING; successor required.
- Astra: 0. No production semantic changes.
- Untracked replay-constructor drafts and `tools/__pycache__` remain quarantined and excluded.

This closeout records a precise compiler failure; it does not count as a closed parent condition or working compiler path.
