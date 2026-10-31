# Independent review — EFFECT-PERMISSION-AUTHENTICATED-SITE-EXPORT-20261028/r1

Reviewer: `/root/canonical_export_final_review` (fresh nonauthor, read-only)  
Verdict: **bounded invocation-2 identity/delegation evidence and conditional Lean results accepted; sprint INCOMPLETE.**

## Findings

**Major — invocation-1 input inventory is missing.** Rust handoff rev3 records the 271-entry inventory hash `0894dc924354a2bc731b469c433b3d1beeba9e922b1baf441afdd6a264ff92c6`, but those bytes are absent. The only retained `input-inventory.json` is the amended 272-entry inventory for invocation 2. The hash cannot authenticate or reconstruct invocation 1's historical source set. Keep this provenance gap open; no reconstructed substitute is accepted.

**Minor — stale execution wording in Rust handoff rev3.** It still calls the current source unexecuted even though invocation 2 ran it. The frozen handoff remains preserved; this primary outcome supersedes those statements.

**Minor — tautological memo-witness assertion.** A hit's witnesses are checked against a union that includes the same hit, so this predicate alone cannot reject an unrelated witness. Other constructor/row/site/port joins provide bounded evidence. No injected-mutant execution was performed; source predicates are not mutation runs.

## Accepted bounded evidence

- All four prior structural defects are repaired: identity equality is separated from the preserved unequal assertion; constructor input is snapshotted at the actual executing HIR boundary; delegated order uses constructor, owner, occurrence, parameter, enclosing coordinate, full path and nested row; observation-only data is absent from non-test signatures/call paths.
- Invocation 2 passed the exact combined identity/two-site-delegation test. The source tree and ordered Function/Tuple Effect-port visits matched; root rows were retained as source data without inventing root-port visits. Both origins joined through allocated row, canonical capture, materialized row node and exact-owner exported port. Two sibling delegated sites retained distinct paths/rows and per-site port orders.
- The five falsifier predicates were reached as assertions against fixed evidence: q/captured-row correspondence, distinct origin concrete sets, exact owner, both origins, and sibling port mapping. No injected mutants were run.
- Invocation 1 reached and passed the bounded identity joins but failed at `state remains in the returned computation` before delegation. This consumer-path finding remains unexplained and OPEN. The original `r != q` and consumer assertions remain in their original unequal path and were not run by invocation 2.
- Lean's ten theorem roots passed full type and transitive-axiom audits. The traversal/EffectVisit equivalence is axiom-free; conditional extraction remains conditional and no native instance was fabricated.

## Lean theorem audit

`port_path_nonempty`, `source_visit_lookup`, `source_visit_unique`, `root_row_separation`: `propext`.  
`constructor_to_source`, `source_port_to_constructor`, `constructor_iff_source_port`, `omitted_port_iff`, `bare_element_not_port`: no axioms.  
`extracted_port_and_export`: `propext`, `Quot.sound`.

All ten complete printed types are retained in the Lean audit stdout. Actual Rust extraction, snapshot authenticity and source/native parent closure remain OPEN.

## Invocation and artifact receipt

| Run | Result | Wall | Peak RSS |
|---|---:|---:|---:|
| Cargo 1 | exit 101; consumer assertion failure | 61.11 s | 1,671,992 KiB |
| Cargo 2 | exit 0; one exact test passed | 6.53 s | 1,122,284 KiB |
| Lean 1 | exit 0; ten audits passed | 12.48 s | 970,236 KiB |

Cargo total: 67.64 s of 180 s. Runs used CPU0, one job/thread, offline/locked inputs and separate raw streams; RSS ceilings were measured, not OS-enforced. The proof output has 10 ordered audit blocks; Lean project/external inventories rehash with zero mismatches. Rust invocation 2's 272-entry inventory rehashes with zero mismatches. Invocation 1's 271-entry inventory is missing as stated above.

Authenticated artifacts:

- Base contract `4088b7dc1d357f1eb531d76ea01951630e8baf2b092856936c4e0a65f2ed77b9`
- Amendment 01 `617f32e2ebabc9c4e98676f3d0c84e6b17b811c50729dc03c312c9744b03c32a`
- Rust handoff rev3 `74471cfb8390bb6beedaa495324335ab6ff0573dc8688402e60e8bf636339112`
- Lean handoff rev2 `dca659627a35ccacc47ae9eec06c0e94a3f3749eb729dc1f833f2d66e86dea91`
- `candidate_effect.rs` `6f20ac00deb2f5a84f57a0cf54cf9ceb64f2de5a90d15cc371240d9de68dfa3b`
- `candidate_scheme.rs` `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`
- Lean source `d6fc3e11f26350f6cf03d7afc248500778e3bf4a8ee816582630aa5f5feeeb84`
- Rust invocation-2 inventory `8b6f6a5addda6d3e8e65d35e6f34e8ee4311069433a6220717811a104d9cf17b`

All original parent/source-native/A/B/unequal-transport/consumer/hygiene/principality/termination/production gates remain OPEN. Reviewer performed no edits, builds, tests, Lean/Cargo, Git operations or descendants.
