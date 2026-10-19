# R75: C1 identity and provenance fidelity

Status: proposed by Luna for immediate activation after exact-pin and state
reconciliation. This packet does not inherit R74 budget.

## Parent and fixed task

Continue the computation-forwarding preservation investigation under principles
§§1, 6–7 at the exact fixed ordinary source, helper local and C1 cut recorded in
R74. Full inference/evaluator and Simple-sub A/B remain OPEN 0→0; R50 remains
NOT_ADOPTED. The R74 closeout is
`notes/progress/2026-10-19-r74-closeout.md`.

R74's test-only observer reaches the intended helper once before its first
LocalUse step, with cursor `(0, None, false)`, and the sole authorized retry
passed. Its ledger is **not accepted as complete**: Debug output elides
constructor-owned definition identity, occurrence artifact brand and parameter
owner. R74 rev2 also incorrectly says the frozen proof artifacts contain a
mistyped contract hash; both contain the actual rev1 hash. Preserve all R74
bytes and receipts.

## Required outcome

At the same cut and without changing solver behavior, produce a detached,
typed identity ledger that:

1. Assigns labels by authentic identity equality, so equal references share a
   label and unequal references never do. Keep definition roots, occurrences,
   source roots/locals, parameters, and other identity families distinct.
2. Includes an owner dictionary resolving every relevant identity to its
   constructor-owned HIR source object and exact available source position.
3. Inventories every identity-bearing reference in the C1 snapshot and proves
   complete coverage. Preserve raw physical vectors, actual map keys, group
   order, source sets, generations, replay/restoration state, and bounds.
4. Establishes successful-path observer erasure for the fixed snapshot and
   identifies any guarantees that hold generally for the collector.

Do not add production code, modify source semantics, canonicalize solver keys,
change solver order/control flow, or alter existing expected outputs. Stop if
an authentic identity cannot be distinguished or mapped to its owner without
inventing identity.

## Exact leases and owners

- Luna, implementation and sole integration: test-only portions of
  `crates/yu-solver/src/candidate_c1_observer_tests.rs`,
  `crates/yu-solver/src/candidate_scheme.rs`,
  `crates/yu-solver/src/candidate_context.rs`,
  `crates/yu-solver/src/candidate_intrusion.rs`.
- Sol/high proof lane: `notes/theory/2026-10-19-r75-c1-identity-fidelity.md`
  and `tasks/agent-loop/inbox/20261019-r75-proof.md` only.
- Luna integration receipts: `notes/progress/2026-10-19-r75-c1-identity-ledger.md`,
  `notes/progress/2026-10-19-r75-c1-ledger.txt`, and
  `tasks/agent-loop/inbox/20261019-r75-implementation.md`.
- Luna owns `tasks/agent-loop/current.json` and this contract. Fresh compiler
  and spec reviewers receive read-only access to one frozen snapshot after
  implementation/proof freeze. No worker commits or pushes.

## Evidence pins

R74 baseline HEAD: `d21c8eb3a87e43dd441474c9f138e71b1d8372ff`. Final code:
`candidate_c1_observer_tests.rs` SHA-256
`350637d7532d0b5c3fadce01f2ae6e4b333d43f99fc713581a0df992daa626c7`;
`candidate_scheme.rs` `5529c61b3132e92d1dffa52ed230727760c47384c43f8910dd53f6228a419f93`;
`candidate_intrusion.rs` `7ff356632f3d665747d14ad1e0013a35c3a27e80de16564d5fefcdbf07ad14f2`;
`shadow_apply.rs` `b28193a5141b019afd6e10766dd77f86366f7a3c04e822b2a4fce784673b665b`;
`lib.rs` `b90eeb2ce7ff78731ce418313fd9fb54b91283d90ae6462723186fde5c0045b0`.
R74 artifacts: ledger `c0b8b21269e4ce997bc698c3ead5793d9a175bbf2bc309e27db7cfa5d8b8af91`;
implementation note `66096a129ea994ad6765f74aecd5703cfe34956a0dd1039e5f943418e6bef77f`;
implementation inbox `a309056bcb2780f3d32c9d405046a703e023309c3d659017d8c8b0676b5513f7`;
proof note `08d7982542ce3119839c71405c2a78597bd124d4adc1050a9e66185ca06c92bb`;
proof inbox `74d9d5f8ae831407a3020d647dd434bdf3fbef08a285330add5bffe83220ad3c`;
rev1 `9b225304040b8ff11b1f1cb79876de136ce0400d69c68fef87bf07288f2c8a25`;
rev2 `3f120e183639c63315cbf22897a56a4215ac4c88ed7c96bfd0e26ffc5f0a3bf3`.
R74 closeout SHA-256
`084eeb8aac1693b293addf501453115aba1fa3bad460fc887ebd78b040098504`.
Existing identity-owner APIs are pinned in `crates/yu-hir/src/module.rs` SHA-256
`c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a` and
`crates/yu-hir/src/shadow.rs` SHA-256
`460c813cb0d2e21565df011b1d816abbc2b180cef13797a1b7b453e9ee413f66`.
These expose identity equality/ownership checks and exact source-position
lookups; labels must be derived from those actual identities.

## Resources, checks and stop conditions

Total cap: 2400 seconds, charged at activation with no R74 carryover: Luna 900
seconds (includes exactly one focused execution of at most 180 seconds); Sol
proof 600; fresh compiler review 300; fresh spec review 300; Luna integration
300; Astra 0. One test command is permitted only after the observer is frozen;
any failure, timeout, or compile error ends execution authority with no retry.
Static checks may inspect frozen bytes but are not independent review.

Falsifiers: unequal references share a label; equal references receive
different labels; an identity lacks an owner or position promised by its source
constructor; any relevant reference is omitted; the collector changes solver
state/order; or a reviewer finds a major fidelity defect. In any such case,
stop, preserve evidence, and keep the result OPEN.

Only Luna adjudicates, stages explicit paths, commits, and pushes. No parent,
Simple-sub A/B, source/native, evaluator, or production gate is promoted by this
packet.
