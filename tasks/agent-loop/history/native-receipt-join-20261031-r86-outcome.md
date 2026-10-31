# R86 outcome — failed exact-input audit; next proof route revised

Sprint: `NATIVE-RECEIPT-JOIN/20261031-R86`.
Contract SHA-256: `fbba407ea6a59e2a0856a369e8e8ea815766c3e241460fe3ea84fa493343453b`.
Input manifest SHA-256: `511553a67c35cd9c9adf90230eae422f8418a12ffe952fb5223266a6f76d0377`.
Final authorization commit: `119572fff`.

## Disposition

**FAILED_AUDIT_CAP_EXHAUSTED.** Both authorized Lean calls were used. Slot 2
exited 1 with seven unsolved-goal errors and error-recovered `sorryAx`; there is
no third call. This is an incomplete proof, not a refutation or source
counterexample. The two call inputs and full raw streams are retained. The
candidate's original R57/R84 statements and definitions were unchanged across
the one reviewed repair.

## Exact execution and independent audits

Slot 1 authorization was committed/pushed at `c3c34e2a9`. Input: 145,333 bytes,
SHA-256 `8cddd5e4c4c1fe27469cc488c6e8522213a6275a598adba2b3b1332959ba10c8`.
Lean 4.35.0 exited 1 without timeout in 16.586 seconds; peak child RSS
931,540 KiB. Stdout: 191,721 bytes, SHA-256
`8646f5e3ea4677ade6c2398807f36dd2e61aa401056fdb2252b05ffd1e790edb`; stderr
empty. Raw result SHA-256 `dbcdcba9347eba214f39970641aabf06064d399b68da5b1fc65ba2d7d45e7138`.

Slot 2 authorization was committed/pushed at `119572fff`. Input: 146,667 bytes,
SHA-256 `2676ee6501c9b7ef3a19003658ee19a2c4f1cdd5c08d3d7a80bd9ba57ee68ab0`.
Lean 4.35.0 exited 1 without timeout in 14.788 seconds; peak child RSS
930,940 KiB. Stdout: 178,056 bytes, SHA-256
`549877d9436f544e7451940d31f19eef444c2893962f28fc41c421ea6f0f9fed`; stderr
empty. Raw result SHA-256 `bc62465e0fdeeeaab6bdd346fb4830f5dfee0058f0de4b146129438f1136582d`.

The slot-1 output review
`tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-slot1-review.md`
SHA-256
`369652edc0c584ddda16dea4bc22361c54fbf6a57b3a9af05e757c64fcb52f2f` records
seven failures; 29 other R86 declarations had clean declaration-level
reports. Amendment 02 added the singleton equality helper and repaired the same
seven proofs without changing their statements. Slot 2 showed that the helper
itself is clean (`[propext]`) but the seven proofs still contain a dependent
`readJoin.match_3` over the indexed Origin read. The supplied read equation
does not reduce that matcher.

The slot-2 output review
`tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-slot2-review.md`
records all 37 R86, 13 R84 and 11 R85 type/axiom pairs, seven errors and 39
warnings. Seven R86 declarations depend on `[propext, sorryAx, Quot.sound]` and
are rejected. The other 30 have clean declaration-level reports under their
conditional scopes: 3 use no axioms, 4 use `propext` and `Quot.sound`, and 23
use `propext` only. These do not make the overall gate pass or establish reader
acceptance.

## Source result and limits

The amended source report is
`tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-source.md`,
SHA-256 `1c066cf341144d176f82452504fe59a9dfed24b01b9da1b55f53535b7d932d5d`.
Within admitted inputs, the producer attaches `completed=false` and appends a
separate completed clone. Both Internal root consumers require the attached
receipt itself to be completed. The cut publication selector checks uniqueness
only inside its saved windows; the whole-root selector requires global
occurrence/pair uniqueness. R57 relation-ID uniqueness is a third, distinct
condition.

Amendment 01 inspected the exact nested defaults/initialize and checkpoint /
rollback chains; those named chains were closed as source text. Whole-crate
transition exhaustiveness, native payload and pointer correspondence, saved
projection authenticity, selector bridges, original A/B, standalone module
imports and production remain OPEN. No Rust code was changed.

## Next bounded outcome

The dispatcher recommends a materially different proof method: model the
actual full, cut-window and Internal readers separately as finite data-returning
functions, then prove relational branch specifications with explicit equations.
Construct dependent certificates only after the relational result is
established. Keep full-inventory versus cut-local uniqueness distinct and apply
only checked results to unchanged R57/R84. In parallel, inspect
`candidate_context.rs` and `candidate_receiver.rs` together for one coherent
owner-local producer/consumer proposal. Until original Root compatibility is
adjudicated, the source lane grants no safe code-edit slice.

No environment, worktree, cache, target, build, test or Rust edit was created
for R86. The user's unchanged Yulang soundness goal continues in a separately
admitted R87 contract; R86's exhausted call budget is not renewed.
