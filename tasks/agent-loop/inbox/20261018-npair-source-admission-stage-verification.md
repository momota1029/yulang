Sprint-ID / contract revision and SHA-256: `npair-source-admission-correspondence-20261018` rev1, `fdbc808bafb8d32df8f86701f41923fbaaf25de91764fdaf65429aa02da6ed25`.
Assignment-ID / handoff revision: `NPAIR-SOURCE-ADMISSION-STAGE-VERIFICATION-20261018` rev2.
Parent gate / original theorem and scope locator: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; preserve source domain/quantifiers; parent closure0.
Baseline / direct dependency hashes: baseline `a5ac0942313e34fac178221a17a1501ed55bc6c2`; adopted contract `692aa39ec37f522e921634134551dad1933b736e5afd2eff463213970a0fb609`; prior candidate `74a83e04a3ecc88a8711ae9ffb2d2bc7274f40eaa2f7eb789ebb0c0980354067`.
Role / worker / session: Luna primary `/root`, current session; writer remains primary only.
Requested/observed model: Luna/high requested; observed UNKNOWN.
Exact lease: write only `crates/yu-solver/src/candidate_source.rs`; no syntax/HIR writes.
Outcome class: implementation evidence continuation; no new theorem claim.
Review finding: independent compiler and spec reviewers each found the previous test helper merged HIR and solver errors, overclaiming solver-stage refusal for empty/mixed forms. Predicate/scope were clean. See preceding final verification record and reviewer replies in the session.
Repair: make `solve_formal` unwrap/require HIR success before returning `CandidateInference::solve`; retain explicit HIR `StructuralProjection` check for the multiple-symbol row.
Final evidence: exact focused test ran 1 passed/0 failed. Empty/mixed inputs explicitly lower to HIR before solver refusal; multiple-symbol is a separate HIR-stage refusal. Final candidate SHA `4ea9d89e4a31e7be4ce170517e50eea31dd9e054c360cedba9ccc9cb7ced69ce`.
Required path: normal parse -> HIR -> solve for adopted target; HIR success -> solver refusal for empty/mixed; HIR refusal for multiple-symbol row.
Resource envelope: +420s; cumulative4980s; primary90, one exact Cargo run120, fresh compiler review60, fresh spec review90, evidence/integration60; Astra0.
Next: one focused target run, then freeze and obtain fresh independent delta reviews. Any failure stops without another fixture retry.
Writer STOP / Git: after test, freeze code and receipt; no commit until new reviews and Luna adjudication.
