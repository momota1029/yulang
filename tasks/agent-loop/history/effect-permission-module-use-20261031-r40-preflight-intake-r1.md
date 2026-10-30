# R40 module-use preflight intake — revision 1

Status: primary intake of a terminal, read-only source report; no research
implementation admitted. Baseline `720eacd38118a1fb408c5886525f3af241f5307d`.

## Source result

The original computation-formal registration is connected to the Lambda
Function's argument-effect child:

1. `candidate_source.rs:1105,2302` creates a source-owned formal registration
   and a fresh entry-effect row for computation formals.
2. `candidate_effect.rs:1841–1900` validates the owner-local Lambda/formal,
   retains the annotation permission with registration/source coordinates, and
   equates a symbolic tail with that entry row at slots 45/46. The concrete
   permission record itself adds no inflow or subtraction.
3. `candidate_source.rs:1767,2464–2467` ties the original parameter Name's
   effect row to the registered entry row at slots 1/2.
4. `candidate_source.rs:2099` retains `formal_registration` on `LambdaRecipe`.
   `lib.rs::admit_lambda_fact` at 11557–11742 uses that registration's exact
   entry row as the positive Function's negative argument-effect child. It
   omits entry-to-return slot 3 for computation formals; body-to-return slot 4
   remains.

The missing relation is later: no retained, permission-consuming witness was
identified from that original formal entry through the particular module-use
instantiation to its actual provider contribution and the selected Catch
residual edge. The receiver withholds Catch slot 51 and traverses its lower
graph, but current suppression checks selection, closed view, family, and
provider/declaration origin; it does not read `formal_entry_permissions`.
Therefore no permission subtraction is justified yet.

Counterexample to a row-equality join: in one annotation scope, two formal rows
`{signal | e}` and `{write | e}` share the memoized symbolic tail, while their
permission records retain distinct registrations and concrete members. The
bidirectional tail equalities do not identify which formal grants `signal`.
This is a constructor-level witness, not a parsed/executed program; it does not
claim eager canonicalization merges the rows.

## Primary dispatch scope-overreach incident

The dispatcher originally authorized reads of `candidate_effect.rs`,
`candidate_receiver.rs`, `candidate_call.rs`, `candidate_source.rs`, and exact
HIR ownership dependencies. It later approved only
`lib.rs::admit_lambda_fact` as a narrow extension. My reader task also named
`candidate_scheme.rs` and `shadow_apply.rs`; the reader inspected both and
reported conclusions that depend on those extra files. The reader followed my
expanded task. This was a primary dispatch scope error, not reader misconduct.

No writes, builds, tests, environment creation, or quarantined-path reads
occurred. Findings depending on the two extra files remain unadjudicated source
evidence. Dependency hashes reported by the reader:

```text
candidate_effect.rs   82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db
candidate_receiver.rs 620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3
candidate_call.rs     fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f
candidate_source.rs   96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a
candidate_scheme.rs   31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707
shadow_apply.rs       c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff
lib.rs                ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07
admit_lambda_fact     a76cfc6305d61af15a2e751efe2fbb59ddaa181b72d066a1256fe7b3187fdc56
```

The reader's final report is Luna's intake, not independent validation or a
Lean theorem. Its exact elapsed time was not measured; the previous 240-second
allowance is treated as fully consumed. No residual time is claimed.

## R39 terminal rows archived from compact state

These rows are copied verbatim from `tasks/agent-loop/current.json`. Their
source/proof/review receipts remain in the R39 handoffs and stage ledger.

```json
{"id":"/root/r39_rust","role":"implementer","state":"STOPPED","requested_model":"gpt-6-luna","requested_effort":"high","observed_model":"UNKNOWN","observed_effort":"UNKNOWN","session":"R39","receipt":"R2 frozen: source 82da9265af3bd663443550f4b113816cf2618c56e96014d9298c4563e875e6db; handoff c32634e3ef4a973883a25b6115e77adab9e0229d077c970f84d72e4ad7f1f142; STOP."}
{"id":"/root/r39_proof","role":"lean_prover","state":"STOPPED","requested_model":"configured","requested_effort":"configured","observed_model":"UNKNOWN","observed_effort":"UNKNOWN","session":"R39","receipt":"R2 frozen: module 748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e; handoff aa8a9a8aae5f4b42779bcf752e5e8b5f6bb1e4474b5f4d49254fc58a03b4d5de. Lean4.35 stdin audit PASS, 18 types+axioms; STOP."}
{"id":"/root/r39_review","role":"compiler_referee","state":"STOPPED","requested_model":"gpt-6.1-sol","requested_effort":"medium","observed_model":"UNKNOWN","observed_effort":"UNKNOWN","session":"R39","receipt":"R1 BLOCKING preserved; R2 CLEAN independent delta review and STOP."}
```

R39 references: contract `tasks/agent-loop/sprints/effect-permission-computation-entry-20261031-r39.md`; admission and stage ledger are pinned in the old current-state `active_sprint`; proof and Rust handoffs above. The R38 predecessor remains in the separate prior-sprint record.

## Migration-gate receipt

Independent policy review and conservative inherited-worker/lease
reconciliation were completed in
`notes/progress/2026-10-20-sprint-adoption-reconciliation.md`, committed at
`bc0a4bf4c8fbb69ec19048360d3738ce42107ccb`. Historical UNKNOWN identities and
quarantined paths remain preserved; no cessation or path release is inferred.

## Next boundary

Read-only source evidence establishes Lambda registration to its original
argument-effect child, but not transport to a particular module-use instance.
The next bounded read must locate the FreshUse constructor and exact retained
mapping, or name the first missing provenance edge. A separate allowance is
required; this report grants no reader continuation, implementation lease,
Lean lease, build, test, or environment.
