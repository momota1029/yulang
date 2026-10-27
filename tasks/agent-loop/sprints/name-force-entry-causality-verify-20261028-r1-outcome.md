# NAME-FORCE-ENTRY-CAUSALITY-VERIFY-20261028/r1 — primary outcome

Disposition: **INCOMPLETE overall; static token mechanism accepted within reviewed source scope**. The frozen candidate was not edited. One Cargo command succeeded and the direct Name/Name receipt-to-bind fixture remained intact. A fresh, timed non-author review found no code correctness defect in the bounded immediate-return token mechanism. The runtime causal probes did not establish the original stale-Local counterexample, so no general source correspondence or parent gate closes.

## Execution receipt

- Contract SHA-256 `09bffa6a699efbcc9a4e54faf0d2ec2287d98bc88bf021c53475d36f40408d2d`; baseline commit `7ce561c02`.
- Frozen source handoff revision 6 SHA-256 `c941703360d701e473c9a44f49724947847fa15ab82c6a84dc179a57bc5efdf4`; input hashes matched at preflight, no code edits.
- Exactly one authorized `cargo run --locked --manifest-path tools/inference-playground/Cargo.toml --bin name_entry_trace`; exit 0, tool wall 1.552s, Cargo build 1.61s, one build job. CPU/RSS UNKNOWN. No retries/fallback. Tests=0, Lean/Lake=0.
- Direct trace remained: completed `ValueHandle(2)`, owner 1, Name occurrence 8, receipt 0, source cell 1, fresh bind cell 2, cell count 2→3.
- Sequence candidate completed with `trace-present`, but it is not equivalent to the reviewed stale-Local `x`→`z` case and the driver only checks whether any historical trace exists. Condition candidate was unsupported by syntax diagnostics. Sequence, Condition, BlockExpression, and the source-qualified stale-Local examples therefore remain dynamically **UNRESOLVED**.

## Independent review

Fresh non-author reviewer `/root/name_force_entry_causality_verify_review`: ACK at 2026-10-27 15:57:42 UTC, completed at 15:59:03 UTC; elapsed 95s of 180s. Read-only; reviewer ran Cargo/tests/Lean 0. Verdict: no new compiler finding; static token lifetime/escape analysis PASS. Reviewer checked candidate hashes, consume, return-frame dispatch, errors, and ordinary ValueEntry eligibility. It found that a token is taken before frame dispatch, never restored, and only a matching ordinary ValueEntry can use it; Local Name consumes clear old eligibility and cannot mint a token. This statically rules out a stale Parameter token crossing those inspected intervening return frames.

The current driver output cannot establish that a particular final entry was or was not attributed, because it reports only sticky trace presence. This limitation and the unsupported/non-equivalent probes keep the causal runtime claim INCOMPLETE. No BlockExpression or original source-qualified example was executed.

The preceding 94s/90s Stage-1 overrun and r2 MAJOR finding remain recorded unchanged; this separate verification sprint did not authorize or erase them. All original parent/A-B, complete Call, native semantic seed/ReturnAlignment, effect hygiene, principality, termination, and production gates remain **OPEN**. The conditional Lean packet remains frozen and audited; no additional Lean work occurred.
