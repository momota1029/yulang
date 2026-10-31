# R77 Rust source lane handoff

Sprint: `EFFECT-PERMISSION-SOURCE-ALIGNMENT/20261031-R77`, contract revision 1
Contract SHA-256: `371b2df095300dfdf942c37530505b53d49fbb114edddb97721e7d54598f8c12`
Assignment: R77-RUST, handoff revision 1
Parent: source/Internal owner-choice construction, bounded by the R77 contract
Baseline: `b500d262a` per Luna's dispatch; dependency pins are from manifest R1
Manifest: `tasks/agent-loop/sprints/effect-permission-source-alignment-20261031-r77-inputs-r1.json`
Role / worker: Rust implementation lane / `/root/r77_rust`
Session and launch receipt: UNKNOWN in this worker context
Requested model/effort: UNKNOWN in this worker context
Observed model/effort: UNKNOWN in this worker context
Lease: `crates/yu-solver/src/candidate_receiver.rs` (only `internal_owner_choice` and Name/Apply coordinate fields); this handoff
Outcome class: implementation candidate; independent review pending

## Behavior

`DefinitionUse.occurrence` is now matched to the callee `Name` reached from the owner-local `ApplySourceInput.expression`, peeling only supported `Group` wrappers. The local `Name` must resolve to the exact `DefinitionUse.target`. Separately, the enclosing `Apply.occurrence` must equal `ApplySourceInput.checking.occurrence`; the Apply's callee and argument must also match the retained input indices, and its cause must identify that checking coordinate.

The constructed choice retains both `callee_name_occurrence` and `apply_occurrence`, alongside the original use and Apply input. Duplicate matching call records and multiple matching uses fail closed. Existing full eligible-origin and recipe scan order remains in place, including the recipe cardinality check before component comparison and immediate rejection of a second matching origin. No Function or effect-row prefilter was added. The formal parameter native root remains distinct from the registered Lambda-root component.

The admitted source shape now has a valid Name-to-Apply join when those source occurrences differ. This only repairs the R76 source-coordinate blocker; it does not alter or waive R76's failed Lean evidence.

## Evidence and checks

- `candidate_receiver.rs`: SHA-256 `9113485e919f41581049a065bef5a533505fc46e71e5d3ae18a4ceec97cdaca7`
- Pinned `candidate_source.rs`: SHA-256 `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- Pinned `lib.rs`: SHA-256 `15e7b131a65f8476eec575d978dc629d15d49e72149325ef35a8c08acc8fc745`
- `git diff --check -- crates/yu-solver/src/candidate_receiver.rs`: passed
- No compiler, Cargo, tests, build, formatter, Lean, or scratch execution was run.
- No scratch or generated paths were created.

## Reused and rejected evidence; remaining boundaries

Reused the R76 source-choice scan and pinned source inventories. Rejected R76's equality assumption between Name and Apply occurrences. R76 Lean audit 2 remains failed, including the recorded `sorryAx` findings; R77 proof work and audit authorization belong to the separate proof lane and Luna.

Rust compilation/runtime, independent review, Rust-to-Lean extraction, genuine R66 `Root`, physical root joins, original A/B, whole-language soundness/principality/termination, and production remain OPEN. No production consumer is connected by this private constructor.

## Stop and next step

Writing stopped after this frozen handoff. No descendants or scratch outputs exist. Next in-envelope step: independent review after both R77 authors stop, then Luna adjudication. This worker cannot certify its own change.

Resource receipt: bounded work stayed within the assigned 600-second lane; exact active seconds are unavailable from this worker context.
