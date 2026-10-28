# Independent review: EFFECT-PERMISSION-CONSTRUCTOR-REALIZATION-20261028/r1

Fresh read-only `compiler_referee` verdict: **BLOCKED for successful
constructor realization; accept only the checked SourceOrigin repair and an
explicitly incomplete research checkpoint.** No parent or production gate
closes.

## Findings

- **BLOCKING — test-only field breaks existing test constructors.**
  `candidate_scheme.rs:214` adds required `Graph.formal_capture_trace_id` under
  `cfg(test)`. Exhaustive `Graph` literals in `shadow_apply.rs:4951` and `:5064`
  omit it and have no struct update. Enabling `shadow-apply-candidate` alone
  would still produce E0063. That file is outside this sprint's lease.
  Resolution: a newly admitted packet must either lease and update both
  initializers or redesign identity storage; then obtain fresh compile evidence.
- **BLOCKING — constructor refinement does not compile.** The final
  `ConstructorRealization.lean` has invalid indexed-case binder lists at lines
  34–35 and 70–77. The final check exited 1 before any of its 11 extension
  declarations received type/axiom audits. The invocation allowance is
  exhausted. Resolution: preserve failure evidence and authorize a new bounded
  repair/audit packet.
- **MAJOR — ordinary-source execution evidence is absent.** The only Cargo
  argv omitted `--features shadow-apply-candidate`. Raw stderr records five
  errors and exit 101; stdout is empty, so zero tests ran. Resolution: after the
  missing struct fields are addressed, obtain a newly authorized
  feature-correct invocation. Do not retry under the exhausted r1 contract.
- **MAJOR — proposed assertions do not prove the wrong-image falsifier.**
  `formal_effect_permissions` already obtains returned ports from the exported
  graph. Membership therefore does not prove the constructor's allocated row
  maps to that port. Symbolic event assertions do not tie memo keys, both
  delegated allocations, row identities, and bounds to a particular capture
  identity and owner export. Resolution: carry the same witness from
  constructor allocation through canonical row/port image and exact owner
  export.

## Checked and unchecked Lean declarations

The repaired `YulangClosure.FormalPermissionSourceOrigin` final hash
`db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd` passed
invocation 1 with complete type and transitive axiom output for all 12:

- `[propext]`: `memo_hit`, `memo_miss`, `signature_pair_closed_allocation`,
  `port_origin`.
- `[propext, Quot.sound]`: `construction_origins`,
  `tuple_construction_origins`.
- `[propext, Classical.choice, Quot.sound]`:
  `constructed_catalog_export`, `pop_write_lifo`, `discovery_membership`,
  `canonical_function_publication`, `empty_indices_no_arrival`.
- No axioms: `parameter_capture_identity`.

All 11 declarations below are **NOT_CHECKED / NOT_AUDITED** because the final
module did not compile:

`effect_memo_refines`, `signature_event_refines`,
`signature_pair_event_refines`, `port_event_refines`, `port_event_birth`,
`value_events_refine`, `tuple_events_refine`, `value_events_birth`,
`tuple_events_birth`, `event_origins_and_births`, `event_catalog_export`.

The event relations do not directly assume `Origin` or `Construction`, but are
manually defined abstract histories. No theorem decodes every successful Rust
constructor into them. Native allocation at `candidate_effect.rs:1388`,
delegated attachment/context at `:2312`, and actual bound insertion at `:2330`
remain unrepresented. Birth-list membership does not prove global freshness or
nonaliasing. Discovery requests remain supplied inputs; canonical publication
requires both the fixed-key equation and actual endpoint membership; catalog
export is distinct from live graph/native permission export.

## Resource and STOP receipt

All seven final assignment hashes matched. The reviewer independently checked
the 46-entry Lean frozen manifest with zero mismatches.

- Rust: exit 101, zero tests, 23.78s, 522,452 KiB RSS, one pinned CPU; launch
  headroom 23,900,647,424 bytes. Required feature was omitted.
- Lean invocation 1: exit 0, 9.11s, 969,360 KiB RSS.
- Lean invocation 2: exit 1, 4.40s, 731,944 KiB RSS.
- Lean invocation 3: exit 1, 1.00s, 762,304 KiB RSS.
- Lean final check ran no extension theorem audits. All invocation allowances
  are exhausted despite unused wall-time budget.

STOP: reviewer was read-only; no edits, Git, builds, tests, Lean, child agents,
or continuing processes.
