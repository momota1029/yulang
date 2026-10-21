# R246 — R187 source/capture qualification

Status: completed static audit; R245 remains conditional; parent/R71/R72/production OPEN.

## Question and evidence boundary

R245 needs complete same-use evidence before its conditional row assignment can be called a source-qualified non-implication. This audit read the frozen R187 observer test, R217/R244/R245 records, and current observer/candidate source owners. It did not run the test or edit code. The source pins are recorded in the R246 contract. The test source is evidence of what would be checked if run; it is not a receipt that those checks ran. Diagnostic print statements are not a retained runtime artifact.

The existing fixture is `relay_capture_snapshots_join_existing_bound_emissions_and_source_sets` in `crates/yu-solver/src/shadow_apply/local_source_observation.rs`. It parses the R187 source fixture, checks no structural recoveries, selects the Apply at occurrence 18, confirms its form is Apply, and asks the candidate solver for the local source-provider observation. The assertions establish complete facts and origins, an untruncated capture result, one observed route, and a complete predecessor snapshot for the relevant Effect(31) row. They also assert the exact Lambda occurrence-12 slot-4 source relation `Effect(10), Negative, Effect(31)` is captured with expected lineage, a local capture-row owner, and a FreshUse image. The test asserts coverage of four separately named `target_bounds`; these are not the missing inner Apply/Lambda chain.

The test prints source admissions, physical emissions, source-origin/drain receipts, captured rows, their images, relation lineage, captured effect bounds, and replay dependencies. It does not assert a complete captured-bound inventory or that the inventory contains the required same-use relations `n_u <= t_b^v`, `r_b <= c_u`, `c_u <= q_u`, and `q_u <= r_u`. In particular, `captured_effect_bound` and `replay_dependencies` are printed, not checked against a complete expected set. There is no asserted join from those rows through the exact Apply endpoints and the actual FreshUse map for the full chain. The four `target_bounds` assertions establish only the four listed bounds, not this missing chain.

## Frozen result coverage

R217's retained result reports the post-change slot-4 q<=r capture edge and its owner after the reverse-owner index change. That is useful evidence for the repair's narrow claim. The retained R217 note does not contain the complete R187 captured-bound list, complete contexts, replay inputs, map entries, or all actual inner and outer Apply endpoints required to qualify R245. The test's diagnostic code would print several of these if executed, but no complete post-R217 stdout/stderr artifact is present in the frozen result records inspected here. Historical R212/R213/R209/R210 material predates the R217 route change and cannot fill that gap.

The source owners and R245 audit separately establish the structural issue being investigated: `Graph.bounds` restoration applies to captured entries through the FreshUse map; the outer Apply contributes endpoint joins but does not recreate a missing mapped middle relation. R245 therefore remains a conditional non-implication for the inspected candidate captured-use graph, not a complete source-qualified solver model. This audit does not establish that the historical solver run admitted the proposed valuation, does not establish a language-level counterexample, and does not refute the parent theorem.

## Result

Frozen post-R217 evidence proves the exact slot-4 capture repair reported by R217, but does not prove the complete same-use admitted slice needed to adjudicate R245. The missing artifact is a complete post-R217 same-use observation/result that retains and checks the full relevant source-bound and owner inventory, the context/replay inputs, each FreshUse map image, and the inner and outer Apply endpoint joins in one joined slice. R246 did not execute the existing test because its contract is read-only. Any such execution or observer expansion needs a new exact contract and authority; until then R245 stays conditional and parent/R71/R72/production stay OPEN.

No tests, builds, samples, code edits, observer edits, or fault injection were performed. Static validation only: `python3 tools/agent_sprint.py check` and `git diff --check` passed. These checks do not execute or validate the source observation.
