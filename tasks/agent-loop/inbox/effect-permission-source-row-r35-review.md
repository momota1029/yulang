# R35 independent review — blocking polarity mismatch

Reviewer: `/root/effect_permission_r31_review`; read-only. Observed model/effort and aggregate elapsed: UNKNOWN. Review used frozen source and proof artifacts pinned below. No builds, tests, environments, scratch, quarantined reads or source edits.

## Verdict

**BLOCKING: Rust and Lean assign different composed polarity to the same formal annotation paths.** Other reviewed source-identity, row-payload, Lean-construction, and conditional downstream-translation claims pass. No additional major/minor findings.

## Blocking counterexample

`tools/inference-playground/src/runtime/program.rs` `from_lambda` starts traversal at `SourceTypePolarity::Positive`; `SourceCallbackPermissionR35.lean` starts the formal contravariantly and records `pathPolarity true path` as contravariant. For `cb: () -> [signal] int`, path `[Result]` is positive in Rust and contravariant in Lean. For a function-valued formal's argument row, `[Argument]` is negative in Rust and covariant in Lean. Both traversal functions flip function arguments and preserve result/tuple descent, so the discrepancy holds at all corresponding paths. No relative-polarity conversion is defined or proved; recomputation authenticates the Rust convention and does not detect the mismatch.

Minimum repair: start Lambda-formal traversal at `Negative`, retaining existing path descent and the Lean formal convention. Do not weaken the Lean convention. This is a bounded source/proof correspondence repair and does not change annotation semantics.

## Findings that passed

- Witness issuance follows retained HIR Arc/root/occurrence lookup, requires a Lambda, and checks formal/annotation ownership and source positions.
- Authentication reconstructs and compares the retained identity/path/payload. Foreign formal, owner, and position substitutions reject.
- Structural paths retain nested function/tuple rows. Concrete vector order and duplicates and every symbolic variable are preserved. Failed construction exposes no partial inventory.
- Lean constructively derives owner→root→expression→Lambda→formal→annotation→path→row and checks exact inventory equality. No assumed row-authenticity law was found.
- Concrete-only translation requires authentication and an empty symbolic vector; nonempty variables reject. Its finite R34/R33/R32 bridge proves exact row/coordinate facts. It does not establish semantic callback-row selection, Grant/request emission, or native execution.
- Fresh independent pinned Lean 4.35.0 stdin audit: 22 theorem types, exit 0, empty stderr/diagnostics. Six use `propext, Quot.sound`; sixteen use `propext`; no holes, project axioms, `native_decide`, or kernel-check bypass. Failed proof attempts 1–5 were retained; attempt 6 passed. Lean-to-Rust vector traversal simulation remains open.

## Frozen hashes reviewed

| Artifact | SHA-256 |
|---|---|
| `program.rs` | `483073deba4619e82e6ff821108c23b45bca9b14cbf2065570f7e5fca38273bc` |
| Rust handoff | `ef5adf7b2f392163f96de5ea8adfecacb8d0b91082f2ebc6bbc67024524c4865` |
| Lean module | `f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9` |
| Proof handoff | `8f4748d48d649afeee3e7959c95fd095bc13840dfcc03e8263d19349bf0a012e` |
| Contract | `b222bb668f9c8f872dfc83a19c48c8ed937a6c5894f6e8ab5b50c5ef468ce570` |
| Manifest | `a9ef98acf98751e603046fe0c4f64ad107373513d6dd0c33c483a2ff235e1205` |

## Still open

Rust compilation/runtime, Lean-to-Rust inventory simulation, consumer integration, callback-row selection, Grant/request/History, selected-arm provenance, observations authentication, invocation lifetime, native `Step`/`History`, original A/B, whole-language hygiene/soundness/principality/progress/termination, and production remain OPEN.

Reviewer STOPPED; writes stopped; no descendants.

## Polarity repair delta — PASS

Reviewer `/root/effect_permission_r31_review`, read-only follow-up; STOPPED with writes stopped and no descendants. The blocking finding is closed: Rust now seeds formal traversal `Negative`, matching Lean's contravariant formal convention. `Function.result` is Rust Negative / Lean contravariant; `Function.argument` is Rust Positive / Lean covariant. Reversing only the seed change reproduces the previously reviewed source hash; no other source change occurred. The refreshed Rust handoff matches the corrected convention. Prior identity/payload/Lean construction and complete axiom audit findings remain valid.

Verified repaired hashes:

| Artifact | SHA-256 |
|---|---|
| `program.rs` | `9565c6e3cd8abfdb6386a7a224e5ea31acd2e9dd5ce4b8891ded04e451f4c436` |
| Rust handoff | `65e53f89c514de2e49d14951a9fe11ed0b2bb41b3ed635d012308b9459c0455f` |
| Exact source diff | `09ea51ff786de5079b6e4508d872f4c73ac9bb0645f594e9ce104bcda3d7d6bc` |
| Unchanged Lean module | `f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9` |

No build, test, Lean rerun, quarantined read, or write occurred during re-review. Rust compilation and Lean-to-Rust vector traversal simulation remain open.
