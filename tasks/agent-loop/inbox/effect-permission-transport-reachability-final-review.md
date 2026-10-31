# EFFECT-PERMISSION-TRANSPORT-REACHABILITY-20261028/r1 — integrated final review

Verdict: **CLOSED_INCOMPLETE**; accept the source-owned backward slice as bounded static evidence. Independent reviewer `/root/canonical_export_final_review` (`compiler_referee`) remained read-only. Luna transcribed this receipt. No edits, builds, tests, Lean execution, Git operations or delegation occurred.

## Backward slice and precise boundary

The slice is authenticated through the frozen source cone:

- `lib.rs:13491` canonicalizes Effect rows through `intrusion.effect_rep`; `candidate_intrusion.rs:168–171` follows the forest.
- Ordinary structural Value dispatch calls extrusion against a receiving Value row at its current level (`lib.rs:14714–14738`). A nested Effect row is copied only when its own current level exceeds target (`candidate_extrusion.rs:94–139`); `original_level <= target` retains the endpoint.
- `retain_extrusion_parent` queues a merge only with qualifying source-event provenance (`candidate_intrusion.rs:324–356`); qualified recapture/activation is separately required (`:393–415`). Settlement processes pending parents (`:570–593`).
- `merge_candidate_rows` canonicalizes both operands, skips equal representatives, then writes `effects[copyRep] = parentRep` (`:613–679`). Rollback restores journaled values; compression preserves an existing class.

The existing recursive fixture at `candidate_effect.rs:3045` is ordinary parsed/lowered/solved source. For its nested formal Effect rows, the current slice supplies no source-established level drop: those rows are allocated at the enclosing parameter Value-row level (`:1815–1849`), and the recursive structural task reaches the `<= target` guard. This is a bounded inspected route, not an execution receipt or proof that all ordinary sources lack the transition.

The first missing source-attributed transition is a demand reaching the same nested permission Effect row with `original_level > target`, followed by a qualifying retained source event and activated pending Parent. A second condition is necessary even if such a Parent is found: the merge writes copy→parent. Extruding allocated r as the parent can create a fresh copy pointing back to r and leave `effect_rep(r)` unchanged. Evidence must show a write that changes r's own representative chain, then join the resulting representative to independently materialized captured q. Qualified Parent retention alone does not show `r != q`.

The internal `source_qualified_effect_extrude` test helper manually selects provenance, seeds processing, directly allocates an Effect row and extrudes at target 0; it is not ordinary-source evidence and cannot fill either missing transition.

## Delegated position mapping

The existing mismatch remains unfixed. `FormalEffectSite` records nested `SourceEffectRow.position` (`candidate_effect.rs:1657`). `SignatureContext::position` returns the enclosing annotation position (`:309`), which delegated tail/port events record at `:2428` and `:2486`. The strict comparison at `:3224` joins different coordinates. Owner, constructor and name do not distinguish multiple nested rows in one annotation. A valid repair must preserve nested-row position and enclosing annotation/occurrence/path separately and establish their relation through the actual source tree, including the shared tail and both allocated ports.

No corrected position mapping or complete native capture/export join was delivered. Previous owner/concrete checks remain bounded pre-failure evidence; prior five falsifier conclusions are unchanged. No new mutation evidence ran.

## Lean disposition

No `FormalPermissionTransportInstance.lean`, scratch output, Lean run, or new theorem audit was produced. The contract conditioned that work on an authentic unequal-transport observation and source position mapping; neither was available. Avoiding another self-supplied fixture was correct. Prior ten-theorem audit remains conditional dependency history only; this review does not claim any fresh theorem/type/axiom check. All parent/source-native/A/B/hygiene/principality/termination/production gates remain OPEN.

## Frozen hashes

| Artifact | SHA-256 |
|---|---|
| Contract | `9318a0697e21e781db875101e781927c91e282b832308ff47d0174846fee58c4` |
| Rust handoff | `d2562c3e8be3ec1633f47adde6add41d4d92bf361b71d25d0eba3582a24cfe5c` |
| Proof handoff | `aa7cc710c2b17c3e3e1f338b3d6ff031024ba264524d739bab0bd31e956b6364` |
| `candidate_effect.rs` | `75d77f44bc9c4efb153fef097fec810d3efba297ae21b1498388a855c676c0d1` |
| `candidate_scheme.rs` | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `Cargo.toml` | `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed` |
| `FormalPermissionExportWitness.lean` | `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f` |
| `FormalPermissionExportWitnessNative.lean` | `a5ccf179ef6e5396adb46c18ced108052cba4022119efd0daa0d026b4c368de1` |

No runtime budget was consumed. Cargo/Lean slots expire with this contract. The precise source-level gap is recorded above; it is not an impossibility result.

**STOPPED.**
