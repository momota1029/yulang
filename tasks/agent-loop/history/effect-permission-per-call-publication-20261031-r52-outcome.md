# R52 outcome — bounded pass

Status: **CLOSED_BOUNDED_PASS**. The independent review found no open blocking, major or minor correctness finding for per-call capture and the conditional Lean bridge.

## Result

Each actual Rust Forward call receives a checked process-local publication identity and its original complete-plan index. The observer records that call's pre-call origin/completion/emission cuts and physical slot, then checks only the corresponding post-return windows. Evidence selection uses `(publication identity, plan index)` before endpoint fields. Observer identity/allocation/evidence failures disable observation without changing successful forwarding. Rust's admitted terminal inventory canonicalizes and deduplicates endpoints before planning.

Lean 4.35.0 Audit 6 authenticated 25 roots with complete theorem types and axiom reports. The independent reviewer reconstructed all six audit byte archives and verified their hashes; only Audit 6 certifies the final module. The conditional model covers key uniqueness, index/cut separation, same-record R51 predicate construction, repeated equal abstract calls, AlreadyPresent with zero prior emissions, missing completion and observer loss. Full producer correspondence is still an explicit premise.

## Frozen artifacts

| Artifact | SHA-256 |
|---|---|
| `candidate_receiver.rs` | `2707cbe4c41a4f91816ef85fe18ac58cc3f5dfe22a648cdcd598215843cb5d4d` |
| `candidate_context.rs` | `c9deb23ebb2b7762f6404c6529231f3581e9959082ee301e03eb1c0895d111eb` |
| Rust handoff | `2183c859ec7b1ce8b75aaf0b93efe4af1c9fdc8012b162833079af03ba8d7cf3` |
| `PerCallResidualPublicationR52.lean` | `d0ffaad36139148c3898d70c9da2e03d1b0e17cbb8b71841f751a8720570e73e` |
| Proof handoff | `da53deb52aed9447c61ef46fb27288cc53e569167221ade7bae5a77d6e58ea6a` |
| Independent review | recorded in `tasks/agent-loop/inbox/effect-permission-per-call-publication-r52-review.md` |

The Lean subprocess ran Lean 4.35.0 with one CPU, `-j1 -M1024`, exit 0, 7.090808 seconds and 910092 KiB peak RSS for Audit 6. No build, Rust compiler, tests, Cargo, Lake or formatter ran under this sprint contract. `git diff --check` passed.

## Scope that remains open

The result is conditional source-level evidence. Faithful same-State Rust extraction, complete owner inventories, cut monotonicity, lifetime/canonicalization, final native reads, whole-publication frame/fact/plan correspondence and concrete Rust execution remain open. So do the original Simple-sub A/B claims, `SourceProblem.InferenceSoundness`, soundness, principality, termination, full effect hygiene and production authority.

The R52 revision-2 contract governs this outcome. Its opening base is `ccdb3e6bb`; the frozen-dependencies section retains historical `b8564a10...` text. The proof handoff records this mismatch, the integration/restart commits (`35eed59f8`, `e9c85710f`) and verified dependency hashes. No dependency drift was found.

Only the exact reviewed R52 source, Lean module, handoffs, review, this outcome and current-state record are intended for staging. Push state is pending primary Git integration.
