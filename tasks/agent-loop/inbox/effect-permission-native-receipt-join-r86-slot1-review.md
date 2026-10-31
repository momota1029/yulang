# R86 slot 1 output audit — FAILED, 29 declaration-level results retained

Reviewer: `/root/r86_independent_review` (`compiler_referee`), read-only.
The reviewer did not run Lean, build, tests or Git.

## Exact invocation and streams

The primary raw result is
`tasks/agent-loop/history/native-receipt-join-20261031-r86-slot1-raw-result.json`,
SHA-256 `dbcdcba9347eba214f39970641aabf06064d399b68da5b1fc65ba2d7d45e7138`.
The reviewer independently confirmed the authorized 145,333-byte stdin hash
`8cddd5e4c4c1fe27469cc488c6e8522213a6275a598adba2b3b1332959ba10c8`, the Lean
executable hash and command, process metadata, and both raw stream lengths and
hashes.

- Exit code **1**, timeout **false**, elapsed **16.586 seconds**, peak child RSS **931,540 KiB**.
- Stdout: 191,721 bytes, SHA-256 `8646f5e3ea4677ade6c2398807f36dd2e61aa401056fdb2252b05ffd1e790edb`.
- Stderr: 0 bytes, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Exactly 36 R86 theorem types and 36 axiom reports, plus the retained 13 R84 and 11 R85 reports. Seven unsolved-goal errors and 41 warnings.

## Failed declarations

The following seven declarations have error-recovered `sorryAx` and are not
usable proof evidence:

| Declaration | Candidate proof line |
| --- | ---: |
| `readJoin_missing_attachment` | 183 |
| `readJoin_missing_completion` | 192 |
| `readJoin_ambiguous_completion` | 201 |
| `readJoin_bad_guards` | 211 |
| `readJoin_accepts` | 222 |
| `readJoinInCuts_ambiguous_completion` | 415 |
| `readJoinInCuts_accepts` | 427 |

All seven residual goals retain the dependent `singletonIndex.match_1` / subtype
selection and subsequent monadic match. The broad `simp` proofs did not
transport the supplied singleton equations to the selected indices. No
counterexample, changed statement, or source-semantic premise was found.

The other **29** R86 declarations have clean type and axiom reports in this
exact flattened input: 3 with no axioms, 4 with `propext` and `Quot.sound`, and
22 with `propext` only. All retained R84 and R85 reports are clean. These 29
are declaration-level evidence under their stated conditional scope; they do
not make the failed slot acceptable or close R86.

## Disposition

The failure is proof-only and plausibly repairable within the one remaining
authorized invocation. Preserve the failed raw receipt. A repair must keep all
definitions and theorem statements fixed, eliminate the dependent selector
explicitly, receive a new amendment and fresh review, and have a separate
committed/pushed exact-input authorization. No third call is available.
