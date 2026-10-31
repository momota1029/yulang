# R77 independent review

Reviewer: `/root/r77_review` (`compiler_referee`), fresh and read-only. Authors were STOPPED before review.

**Verdict: ACCEPT for the bounded R77 research packet. Findings: 0 blocking, 0 major, 0 minor.** This does not certify production or original A/B closure.

## Rust source alignment

The repair addresses the owning join in `candidate_receiver.rs:2364–2405`. It authenticates the enclosing Apply from its receiving owner, checking occurrence, cause, and operands; resolves its callee through owner-local, cycle-rejecting Group peeling; then compares the resulting Name occurrence and resolved ModuleDef target with the DefinitionUse. Retained fields at lines 535–537 preserve both coordinates. It no longer requires Name = Apply.

The reviewer checked this against the collection owners in `candidate_source.rs:1766–1787, 1911–1920`, branded source lookup in `yu-hir/src/module/local_source.rs:174`, the admitted envelope in `candidate_receiver.rs:2942–2975`, and native owner selection in `lib.rs:18328–18385`. The global origin scan retains recipe-cardinality checks before component comparison and immediate second-match failure. The formal parameter native root remains separate from the registered Lambda component. Relevant source-occurrence and receiver tests were read, not run.

## Lean constructor and source correspondence

The Lean constructor reads complete inventories rather than accepting a selected plan or registration. `constructAligned` authenticates an indexed Apply and independently resolves its Name and target; `construct` produces the three premises consumed by the existing R66 seam. `ordered_selection_agrees` proves successful ordered-scan agreement with the actual R66 `ownerSelection`; native failure order is stated separately. Duplicate plans/calls, foreign owners, malformed recipes, second origins, invalid source coordinates, and cyclic/missing/unsupported peel cases remain covered. The constructive fixture explicitly distinguishes Name 100 from Apply 102.

### Checked theorem types

All names are in `YulangClosure.SourceInternalChoiceR77`. Generic declarations quantify over `S T : Type` with decidable equality, source inventories, owner keys, and displayed arguments.

| Declaration | Premises and conclusion |
|---|---|
| `visit_agrees` | `visit.toOption` equals R66's per-origin Option action for every source, target, component, and origin. |
| `walk_accounts_for_all` | Successful `walk origins selected = .ok out` implies rows exist with the complete `origins.mapM visit.toOption` result and `selected ++ rows.filterMap id = out`. |
| `ordered_selection_agrees` | `orderedSelection s target component = .ok c` implies R66 `ownerSelection s target component = some c`. |
| `malformed_recipe_first` | Head visit returns `.recipe c.registration` implies walk returns that error without consuming the tail. |
| `second_origin_first` | Head visit matches and selected is nonempty implies `.secondOrigin c.registration`. |
| `choice_three_premises` | `c : Choice s u receiving target` implies the exact R55 plan equation, R66 owner-selection equation, and selected parameter-recipe equation. |
| `choice_applies_r66` | The same Choice and arbitrary R65 inventory imply those three equations through R65/R66's actual input projection. |
| `exact_use_unique` | Choice, plan membership, and same exact use imply the plan equals `c.plan`. |
| `construction_certifies` | Computed `construct`: none implies True; some `c` implies all three R66 premises. |
| `finite_constructs_choice` | `fixtureChoice.isSome = true`. |
| `finite_bad_inventories_reject` | Seven cases reject duplicate plans, missing parameters, missing/duplicate recipes, duplicate constructions, wrong component, and wrong parameter. |
| `finite_foreign_shared_images_rejected` | A foreign origin sharing Function and entry images is rejected by ordered selection as `.noOrigin`. |
| `finite_native_failure_order` | Earlier malformed recipe returns `.recipe 1`; a second matching origin returns `.secondOrigin 0` before a later malformed origin. |
| `duplicate_plans_rejected` | At least two exact-use plan rows imply `construct = none`. |
| `peel_sound` | Successful finite peel gives `PeelsTo` backed by indexed Name and Group nodes. |
| `alignment_has_name` | Alignment implies source owner = receiving, call owner = receiving, and the callee `PeelsTo` the exact use occurrence and target. |
| `aligned_construction_certifies` | Computed `constructAligned`: none implies True; some `c` implies the resolved Name path and all three R66 premises. |
| `admitted_shape_constructs_distinct_coordinates` | Fixture Name occurrence differs from Apply checking occurrence; peel resolves the exact Name/target and aligned construction succeeds. |
| `finite_alignment_rejects_duplicates_and_foreign_owners` | Nine cases reject duplicate plans/calls, foreign source/call owners, and wrong target/use/checking/expression/argument. |
| `finite_peel_rejects_cycles_missing_and_other` | Four cases reject a cycle, missing index, Apply-as-callee, and other form. |
| `duplicate_aligned_uses_rejected` | At least two aligned use-plan rows imply `constructAligned = none`. |

### Complete axiom census

Only `propext` (8): `visit_agrees`, `malformed_recipe_first`, `second_origin_first`, `exact_use_unique`, `finite_constructs_choice`, `finite_bad_inventories_reject`, `finite_foreign_shared_images_rejected`, `finite_native_failure_order`.

`propext` and `Quot.sound` (13): `walk_accounts_for_all`, `ordered_selection_agrees`, `choice_three_premises`, `choice_applies_r66`, `construction_certifies`, `duplicate_plans_rejected`, `peel_sound`, `alignment_has_name`, `aligned_construction_certifies`, `admitted_shape_constructs_distinct_coordinates`, `finite_alignment_rejects_duplicates_and_foreign_owners`, `finite_peel_rejects_cycles_missing_and_other`, `duplicate_aligned_uses_rejected`.

No `Classical.choice`, `sorryAx`, or project axioms were reported. The changed module contains no proof holes or checker bypasses.

## Independent receipt reconciliation

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| Rust receiver | 278838 | `9113485e919f41581049a065bef5a533505fc46e71e5d3ae18a4ceec97cdaca7` |
| R77 Lean module | 28735 | `0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682` |
| Audit 2 stdin | 48816 | `892da354ef83454c7639036e5910836cae704a9f93861eaa900c45fae34d1244` |
| Audit 2 stdout | 35838 | `815713955fb200025ff4c3b52fb0937ebc4ba278d643f8a0fee273eb3f429a69` |
| Pinned executable | 9024 | `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38` |

The reviewer independently reconstructed all 13 slices, checked complete-source and slice hashes, rebuilt stdin with all 21 queries, and matched retained stdout exactly. All theorem declarations have matching type and transitive axiom reports. The stdout contains no error or `sorryAx` markers. The retained receipt records exit 0, 3.127 seconds, no timeout, and empty stderr. The Markdown empty-stderr code block contains a presentation newline, so it is not itself a byte-for-byte encoding of empty stderr. The reviewer did not independently rerun or observe the Lean execution.

## Remaining OPEN boundaries

Rust compilation/runtime; full imported-project elaboration beyond the exact checked slices; authenticated Rust-to-Lean extraction, including branded identities and complete inventory provenance; genuine R66 incidence/Root and physical root joins; whole-language cases; original A/B; effect hygiene, soundness, principality, termination; and production promotion remain OPEN. Constructor certification establishes successful-output properties, not universal construction success or full Rust/Lean behavioral equivalence.

**Reviewer STOP / WRITES STOPPED.** No files were changed, authors contacted, descendants spawned, Git operations, builds, tests, or Lean invocations.
