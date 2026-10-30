# R37 stage ledger — source-use inventory correspondence

Sprint: `EFFECT-PERMISSION-SOURCE-INVENTORY/20261031-R37`
Contract SHA-256: `33c4c4f1d60e69c11a1a082cbe10a91728888bcdcbf2e11b8f735aa5d14dc756`
Manifest SHA-256: `ca60bdfaf7a2f4e41946a3bb96cd20bd0d223be5f15820bab4843fb99e1d2dae`
Admission SHA-256: `fffeef07ea66c641c46cda06cc4ee0fe92910d924df93139c215bf3cfab211e6`

| Stage | State | Evidence / boundary |
|---|---|---|
| Contract/dependencies | ADMITTED; committed and pushed | Baseline `ce922eed506e1471abe9a0f6823674da7ba55039`; admission checkpoint `e706684c5` pushed to `origin/yulang3`; exact manifest hashes frozen. |
| Rust extraction/inventory | FROZEN; repaired and independently reviewed | `program.rs` SHA-256 `d648e2f180cbe4690d70ee0813d92759929678eb10b4e0973e7b6f7833da91b4`; Rust handoff r1 SHA-256 `f7189a06126c9cb32d483e267d7b293c194f05cf5afc2f8bd25b66c23a7460fb`. Primary routed R35 collector `try_reserve` failures and checked row copies through `Err`; legacy Option wrapper remains for existing consumer. |
| Lean indexed inventory | FROZEN; independent audit PASS | Lean SHA-256 `4981f8c20dc5d9c932d9f4a843f2245c034daaa015e7fc7b97aa7a343bb7ea30`; proof handoff r1 SHA-256 `ded40d8ce118b1403528de519d41ea6c59d7e61d514f8c4b86e1033d8e6f0054`. Pinned 4.35.0 stdin audit exit 0; all 27 theorem types/full axiom sets, no diagnostics. |
| Independent review | STOPPED; technical PASS | Review handoff SHA-256 `a82a806fd419224285ffa19f42d043360379598966081636eeb1c22849fc6937`; all 27 theorem declarations and independent pinned Lean 4.35.0 audit reviewed; no correctness finding remains open. Reviewer read-only, primary recorded receipt. |
| Luna integration/Git | SOURCE CHECKPOINT COMMITTED | `d00417851` contains five exact reviewed outputs; central outcome/current receipt follows. Inspect the full outbound range and push. |

R37 adds no runtime, Grant/Catch, Rust simulation, original A/B or whole-language closure. The R36 unauthorized producer-read incident remains separately recorded; R37 accessed neither quarantined path. Preserve all 32 pending items, UNKNOWN workers and quarantined leases.

## Primary source delta after Rust freeze

The R37 Rust handoff froze source SHA-256 `d2a54ae0409d71ddf384a1c4045188096d3a8b1e610f8b5666de949960337c5a`. Static review found that R35 `from_lambda` collapsed its own `try_reserve` failures to `None`, which would misclassify them through the new R37 API. Luna added `try_from_lambda -> Result<Option<_>, TryReserveError>` and a checked deep-row clone path for the R37 API; the pre-existing Option wrapper remains for its prior caller. Intermediate source SHA-256: `c2a0bc4c35cc1de22f8f05db5330240b2d311fdf4154dfed5aa8ea526c6768f3`; final source SHA-256: `d648e2f180cbe4690d70ee0813d92759929678eb10b4e0973e7b6f7833da91b4`. The R37 API also authenticates through a fallible `try_authenticates`, so R35 row re-extraction errors propagate through `Err`; the old bool wrapper is retained for existing consumers. The frozen Rust handoff remains immutable; both primary deltas are included in the independent R37 review target. No build or tests.


## R37 final adjudication

R37 bounded gate is CLOSED_PASS. Rust source checkpoint `d00417851` is local pending the central receipt push. Final source hash `d648e2f180cbe4690d70ee0813d92759929678eb10b4e0973e7b6f7833da91b4`; Lean module `4981f8c20dc5d9c932d9f4a843f2245c034daaa015e7fc7b97aa7a343bb7ea30`; proof handoff `ded40d8ce118b1403528de519d41ea6c59d7e61d514f8c4b86e1033d8e6f0054`; review `a82a806fd419224285ffa19f42d043360379598966081636eeb1c22849fc6937`. Reviewer's role was read-only; Luna placed the returned report in the leased review path. All 27 theorem audits passed independently. No Rust compile/test was run. Runtime and parent gates remain OPEN.
