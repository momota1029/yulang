# R53 independent review — bounded PASS

Reviewer: `/root/r37_inventory_review`. Both authors were confirmed STOPPED before review.

**No BLOCKING, major or minor correctness finding remains open in the bounded whole-publication observation and conditional Lean construction.** Faithful Rust extraction into the same R50 context/live State, concrete execution and parent closure remain OPEN.

## Source assessment

`candidate_receiver.rs:372–387` now retains one whole-publication owner containing the existing publication identity, relay/answer roots, Catch coordinates, original fact, upper/result row, complete checked plan, ordered calls and initial/final lower vectors. The existing per-call queries project from this object.

The owning checks at lines 1084–1098 bind the original slot-51 fact, its cause, Catch/selected-arm occurrence, raw result row and complete terminal/decision order. The plan and pending fact are the same private objects used for publication; they are not selected by matching endpoints afterward.

Lines 1108–1176 check exact Forward counts and consume calls in original plan order. Each Forward must match publication identity, original index, endpoint, upper, fact occurrence and cause. Suppress positions consume no call. Final cardinality checks exclude missing and extra records.

Each call retains R52’s individual windows. Lines 1165–1174 require well-formed windows, contained origin/completion indices and monotone composition with the preceding call. They do not replace per-call attribution with a publication-wide frontier.

Lines 1113–1118 preserve exact initial lower-vector prefixes. Lines 1178–1250 check the suffix:

- AlreadyPresent must refer to its initial slot and contributes no append.
- NewlyEmitted must occupy the next authorized lane-local suffix position.
- Missing, extra, duplicate, reordered or unexplained suffix entries reject observation.

Lower-row and lower-atom order are checked independently, matching their separate physical vectors. Global Forward order remains retained in the call list. Pre-existing target and same-family sibling contributions are preserved; suppression does not imply global absence.

The admitted source domain remains the canonicalized, deduplicated terminal inventory.

## Failure isolation

Initial snapshots at `candidate_receiver.rs:1486–1525`, final snapshots and whole-publication validation return `Option`. Missing identity, allocation failure or evidence mismatch disables observation.

The ordinary publication path at lines 1007–1072 retains authenticated planning, inherited outcomes allocation and exact Forward calls:

```rust
constrain_live_effect(
    decision.endpoint,
    pending.upper,
    &pending.fact.id,
    &pending.fact.cause,
)
```

Whole capture occurs after successful forwarding and cannot propagate an observation error into solver success. R51 B1 remains closed.

`candidate_context.rs` is unchanged from the accepted R52 pin. No new producer history or second identity scheme was added.

## Lean result and its premises

All 28 actual declarations, statements, bodies and final printed types were inspected.

`assemble` consumes the complete plan and exactly one record per Forward, preserving Suppress positions. Induction derives ordered projections, both Forward/call directions and suppressed-call absence.

`aligned_item_reads` reuses each record’s same R52 probe. `owner_frame` derives R51’s append equations from direct owner-vector take/drop comparisons. These are checked frame observations, not a theorem that arbitrary successful inference necessarily preserves the frame.

`whole_publication_observed` constructs R51 observation acceptance from:

- the accepted complete R50 plan;
- successful assembly;
- exact keyed inventory;
- per-record source/native reads;
- artifact and original-fact agreement;
- observed owner-prefix/suffix comparisons.

Adjacent cut checks compose into chronology. `source_whole_observed` combines those results, and `whole_exact_native_frame` applies R51’s frame theorem to the same assembled query and records.

The remaining premise is substantive: the retained Rust owner must be faithfully interpreted as those primitive reads in **one live State and the same R50 context**. Source brands, lifetimes, canonicalization, complete inventories and actual execution are not proved by snapshot consistency or kernel acceptance.

Complete axiom census, namespace `YulangClosure.WholePublicationResidualR53`:

| Full transitive axioms | Theorems |
|---|---|
| none | `cut_order_trans`, `concrete_assembly`, `concrete_missing_reordered_foreign_fact_rejected`, `concrete_cut_reordering_rejected` |
| `propext` | `assemble_sound`, `aligned_projections`, `aligned_lower`, `suppress_has_no_call`, `forward_has_original_call`, `call_has_original_forward`, `keyLookup_absent`, `owner_frame`, `adjacent_cuts_compose`, `same_state_receipts_separate`, `concrete_owner_reads`, `concrete_prefix_suffix_rejected`, `concrete_reordered_suffix_rejected` |
| `propext`, `Quot.sound` | `aligned_item_reads`, `whole_publication_observed`, `whole_observer_components`, `source_whole_observed`, `whole_exact_native_frame`, `whole_preserves_existing_atom`, `concrete_sources`, `concrete_whole_publication`, `concrete_parent_frame`, `concrete_suppressed_whole_keeps_existing`, `concrete_observer_loss_successful_forward` |

No final `Classical.choice`, `sorryAx`, project axiom or unchecked native-evaluation dependency appears.

## Receipt authentication

All four archived audits’ raw stdin, stdout and stderr were decoded in memory. Every byte count and SHA-256 reproduced. Failed Audits 1 and 3 remain failed history.

Audit 4 contains exactly the 28 current roots in source order and every complete current R39/R45/R47/R48/R50/R51/R52/R53 source once, with only the documented import removal.

Final hashes:

- stdin: `f33b9df1c01a6d1531ff797bb110077f456d2beceb888a5174ef4d34d3858bde`
- stdout: `862d35aefeb67cd1cdb7496e82a9f745e3310ba65c576718d5cd548079dcabf8`
- empty stderr: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`

The receipt reports pinned Lean 4.35.0, one CPU, `-j1 -M1024`, exit 0, 11.679645 seconds and 924,880 KiB peak RSS. No checker was rerun.

## Frozen hashes

| Artifact | SHA-256 |
|---|---|
| Contract | `78321147638d3847c1073c6c24a7050a068c4a5142cc7c8e8206232c6ea4926e` |
| Amendment 01 | `b1cad22e75c360ae8b217b9671cf52f066afab916ef67435117733f0e4b46636` |
| Receiver | `c13aa8543fcf5acb281951badd2edaddfc954c2697d14b701aab337f6b3490fd` |
| Unchanged context | `c9deb23ebb2b7762f6404c6529231f3581e9959082ee301e03eb1c0895d111eb` |
| R53 Lean | `dc9c89e562f905c2c6284fd15eb82e9482a82bc9b2881f567c3454198318f391` |
| Rust handoff | `9fec2edac77ba9dd8d4396e5837839ca7d9fd3d57d6fd6b6eac40e139ec5c5a7` |
| Proof handoff | `b375de22c8f22b183cd1aadf0ef078a33d895ed9116609c52c65e93e62bc987a` |

The amended governance reference, R52 outcome/review/handoffs and final audited model dependencies matched their recorded pins. The amendment changes the referenced document digest; it supplies no semantic or proof closure.

## Boundary and STOP

This PASS covers the checked whole-publication source structure and conditional theorem application. Concrete Rust compilation/runtime, faithful extraction, original A/B, `SourceProblem.InferenceSoundness`, soundness, principality, termination, complete hygiene and production remain OPEN.

Reviewer **STOPPED**. No writes, builds, tests, compiler/checker reruns, Cargo/Lake, scratch files, cache/target/environment/worktree creation, descendants or persistent processes. No quarantined path was accessed or released.
