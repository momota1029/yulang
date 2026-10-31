# EFFECT-PERMISSION-TRANSPORT-REACHABILITY-20261028/r1 — Rust handoff

Sprint / contract: `EFFECT-PERMISSION-TRANSPORT-REACHABILITY-20261028/r1`, `tasks/agent-loop/sprints/effect-permission-transport-reachability-20261028-r1.md`, SHA-256 `9318a0697e21e781db875101e781927c91e282b832308ff47d0174846fee58c4`.
Assignment: Rust backward slice and ordinary-source route classification. Handoff revision 1.

## Parent and source scope

Parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5; original all-supported-source quantifiers remain unchanged and OPEN. Governing annotation policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5. Effect permission is local annotation permission; actual inflow/residual remains constraint-derived. No representative equality is inferred from equal rows, and prior conditional injective-renaming results do not establish this potentially identifying parent/copy operation.

## Frozen inputs and authorship

Requested model/effort: registered implementer, Luna/high. Observed model/effort: UNKNOWN to this worker interface. Worker: `/root/effect_permission_transport_rust`; no descendant workers.

Exact Rust write leases, unchanged at handoff:

- `crates/yu-solver/src/candidate_effect.rs`: `75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1`
- `crates/yu-solver/src/candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`

Read-only pins rechecked at intake: `candidate_intrusion.rs` `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`; `candidate_extrusion.rs` `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`; `lib.rs` `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`; `shadow_apply.rs` `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`; `Cargo.toml` `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`; checked decoder `FormalPermissionExportWitness.lean` `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`; conditional module `FormalPermissionExportWitnessNative.lean` `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1`.

Prior evidence reused: prior Rust handoff `tasks/agent-loop/inbox/effect-permission-canonical-export-rust.md` SHA-256 `ea9d9e74f383adefb120abcc619c8395404e20f41d0f1acc71764df0fba20d8e`; canonical-export outcome `tasks/agent-loop/history/effect-permission-canonical-export-20261028-r1-outcome.md` SHA-256 `f3c634072dd5affadc720af11ed3b6b5ec653d370cbc34cf929520323a84bbc5`; integrated review `tasks/agent-loop/inbox/effect-permission-canonical-export-final-review.md` SHA-256 `4961ea42bb3ad09579ecf0bff2899af1b2d229cb4067d86dfcbc3d9508c687d8`. They establish two focused ordinary-source runs observed only raw/captured row pairs `[(19,19),(21,21)]` and `[(21,21),(23,23)]`; those runs do not establish unequal transport or unreachability.

## Backward slice and candidate source classification

`effect_rep(r)` is a forest representative lookup (`candidate_intrusion.rs:168–171`). The only effect forest merge writer in the leased read cone is `merge_candidate_rows` (`candidate_intrusion.rs:599–679`), called by `settle_candidate_intrusion` for retained pending parents (`:570–593`). It first canonicalizes both operands and returns without a write when they already match (`:613–616`); an Effect parent write occurs at `:675–679`. Rollback/compression are separate writers (`:196–215`, `:512–557`), not source-qualified merges.

The source-qualified write chain is:

1. Ordinary value dispatch can call `candidate_extrude` only for a non-row structural endpoint compared against a receiving `ValueRow`, at the receiving row's level (`lib.rs:14714–14738`). A row endpoint reached recursively inside that structure is classified by its own original level in `candidate_extrusion.rs:94–107`.
2. An Effect row creates a fresh copy and retained `Parent` only after passing `original_level > target` (`candidate_extrusion.rs:103–139`; the `<=` branch memoizes and continues at `:104–106`).
3. `retain_extrusion_parent` indexes that parent in `pending` only when the active extrusion source events include an event for which `candidate_source.references.qualifies(event)` holds (`candidate_intrusion.rs:324–356`). `finish_candidate_extrusion` groups the invocation (`:368–385`); settled activation also requires qualified retained provenance (`:393–415`).
4. `settle_candidate_intrusion` sends activated pending parents to the merge writer (`:570–593`). Only then can a distinct Effect `copy` become a distinct `effect_rep(r)` result.

The existing source test is genuinely parsed/lowered/solved ordinary source, not an internal manual merge: `formal_permission_constructor_owner_domain_graph_export_join` uses the recursive definition `my f(pair:((int -> [io] ()), (int, int -> [io] ()))) = f pair` (`candidate_effect.rs:3045–3064`). The nested negative concrete-only permissions are allocated inside `candidate_formal_annotation` at the enclosing formal parameter's value-row level (`candidate_effect.rs:1815–1849`), and the existing source path performs a monomorphic recursive self-use of that same formal parameter. On this inspected route, the effect-row task reaches `candidate_extrude` with no source-established level drop: the exact first missing transition is the strict `effect_levels[row] > target` branch at `candidate_extrusion.rs:103–107`. When the nested row level is already `<= target`, the code returns the original endpoint and does not call `retain_extrusion_parent`; there is therefore no qualified pending Effect parent for `merge_candidate_rows` to write. This is a static source/owner classification, not a newly run execution trace or a proof that all ordinary source routes fail.

The handoff evidence needed to authorize the requested test-only instrumentation is still missing: one authentic ordinary-source constructor/use whose structural extrusion targets a receiving level strictly below the exact nested permission Effect row, and whose resulting retained extrusion event passes the source-reference qualification guard and activates that Effect parent. A manually constructed parent, the internal `source_qualified_effect_extrude` fixture, a synthetic representative, or a new guessed source fixture is not evidence for that transition.

## Outcome, checks, and limits

Outcome class: bounded source-owner classification; no qualifying ordinary-source Effect merge route established. Exact requested transition: source-generated demand must reach nested Effect `Visit` with `original_level > target`, then its retained extrusion event must satisfy `references.qualifies` and enter activated `pending` before the merge writer. Owner for this missing source-demand/level relation is the ordinary source demand/dispatch construction upstream of `candidate_extrude`; the `<=` level guard itself is in the frozen read-only extrusion owner.

No source file was edited. No Cargo invocation was run; both invocation slots remain unspent in this sprint because contract forbids speculative probing. No check/build was run. No raw run receipts or scratch paths were created. Exact diff contribution is only this leased handoff. The prior r1 observation `r=q` is reused as bounded evidence; any inference of impossibility from it is rejected. Existing later delegated-site mismatch (annotation position used where nested effect-row position is required) also remains open because the prerequisite route was not established and this assignment ended under the contract's stop condition.

Source/native correspondence: nested permission allocation and actual export/capture evidence exist, but no ordinary-source representative-changing transition was witnessed. The actual materialized graph row remains independent evidence `q`; `Origin.concrete`, owner, path, polarity, node and returned port joins from the previous lane are preserved but do not supply the missing transition. All parent, source/native, A/B, hygiene, principality, termination and production gates remain OPEN.

Next related in-envelope step: Luna should obtain a source-owner route/input showing strict level lowering for the annotated nested Effect row and its qualification/activation, or close this finite packet as no-route-found without calling it impossible. If that evidence is not available under this sprint's frozen dependencies, no Rust edit or Cargo run is justified. Writer state: STOPPED; no descendant/generated outputs; exact write leases stopped. No extra paths or disposable scratch were created.
