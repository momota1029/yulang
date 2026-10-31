# R86 Lean slot 1 authorization — exact frozen receipt-join input

Authorization: Luna primary, under the ongoing Yulang Rust/Lean goal and R86
admission. This authorizes exactly one in-memory Lean invocation, after this
authorization and all frozen inputs are committed and pushed. The invocation
accepts no theorem by itself. R86 permits at most two separately authorized
calls; no retry is authorized here.

## Reviewed inputs

- Contract: `tasks/agent-loop/sprints/native-receipt-join-20261031-r86.md`, SHA-256 `fbba407ea6a59e2a0856a369e8e8ea815766c3e241460fe3ea84fa493343453b`.
- Amended manifest: `tasks/agent-loop/sprints/native-receipt-join-20261031-r86-inputs.json`, SHA-256 `511553a67c35cd9c9adf90230eae422f8418a12ffe952fb5223266a6f76d0377`.
- Candidate `notes/theory/lean/YulangClosure/NativeReceiptJoinR86.lean`: 24,130 bytes, SHA-256 `ecad50df44c8db31d8836212a220eacba564aec22c59a3ee3cdcb6e7e96688d6`.
- Proof handoff `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-proof.md`: 14,978 bytes, SHA-256 `69d46ba43b5d97d2096c8c39dab9a556ec8b34dcf269f0cabf0ea0f7c8f99796`.
- Source handoff `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-source.md`: SHA-256 `1c066cf341144d176f82452504fe59a9dfed24b01b9da1b55f53535b7d932d5d`.
- Independent pre-execution review: `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-review.md` (PASS; theorem/type/source review and exact-input reconstruction).

## Exact invocation

The exact in-memory stdin is 145,333 bytes, SHA-256
`8cddd5e4c4c1fe27469cc488c6e8522213a6275a598adba2b3b1332959ba10c8`.
It consists of the previously accepted R85 exact stdin (115,884 bytes,
SHA-256 `bac29ad18bd16e9a5af0422ea4d3416e049a61951d6b1545c8ba35a0548cbc79`),
one newline, the import-stripped frozen R86 candidate, one newline, and the
36 fully qualified `#check @...` / `#print axioms ...` pairs. The appended
query bytes are 5,360 bytes, SHA-256
`cdc414fa5196c857de714c425120370b3b15c5f432e1d1c3259ba2d893179995`.
The complete R84 and R85 query pairs remain in the input.

- Executable: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`.
- Executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
- Version: Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Command: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -j1 -M1024 --stdin`.
- Working directory: `notes/theory/lean`; environment `LEAN_NUM_THREADS=1`; hard timeout 120 seconds.
- Process input is reconstructed and hashed in memory; full stdout/stderr and process metadata are captured in memory. No temporary input, log, scratch, cache, `.olean`, target, worktree or environment is permitted.

Independent pre-execution review passed: `tasks/agent-loop/inbox/effect-permission-native-receipt-join-r86-review.md`.
The reviewed claim is limited to the explicit finite receipt model and its
conditional application to unchanged R84. Source/native extraction, whole-crate
transition exhaustiveness, standalone module imports, original A/B, and
production remain open. Acceptance requires exit 0, exactly 36 new printed
theorem types and axiom reports, complete retained R84/R85 reports, and no
errors, `sorryAx`, project axioms, `Classical.choice` or native-evaluation
shortcut. Any failed/recovered declaration rejects that invocation.
