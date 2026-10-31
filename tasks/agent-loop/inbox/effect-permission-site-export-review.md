# EFFECT-PERMISSION-SITE-EXPORT-20261028/r1 — independent review receipt

Transcribed by Luna from the fresh read-only compiler_referee return after both producers STOPPED. Reviewer ran no builds, Cargo, Lean, tests, Git, edits or descendants.

## Verdict

**CLOSED_INCOMPLETE; Rust artifact needs repair before acceptance.** The concrete Lean traversal passes all ten audits under its printed premises. Rust invocation 2 stops before source-tree/capture/export assertions, and static review finds three further defects.

## Findings

1. **Blocking — original unequal test is unsatisfiable.** `candidate_effect.rs:3263–3271` unconditionally asserts every pair has `r=q`, then asks for some `r≠q` when `assert_unequal_transport` is true. The original test at `:3130–3131` passes true. Keeping the inequality assertion text does not preserve the test contract. Repair must restrict identity equality to the separately selected identity observation and retain the original inequality obligation independently.
2. **Blocking native identity gap — separate-session owner lookup panics.** At `:3169`, the owner from one lowered HIR indexes schedules in an independently parsed/lowered session. The two owner keys differ; Cargo run 2 panicked “no entry found for key” before site/capture/export joins. The analogous lookup is at `:3330`. Matching source text/file labels do not authenticate cross-session identity. Repair must use the same authoritative lowered HIR or prove an explicit identity-preserving mapping.
3. **Major — delegated port order groups only by enclosing annotation.** `candidate_effect.rs:249–252` counts preceding ports by constructor and outer annotation position, although events now retain occurrence, parameter, path and nested row. Multiple nested sites under one annotation get global 0/1 and 2/3, while per-site assertions at `:3400` expect 0/1. Key order by the complete source site or verify the global order without per-site assumptions.
4. **Major — observation-only arguments entered non-test code.** `candidate_signature_effect` has ungated `site_occurrence`, `site_parameter`, and `site_path` arguments at `:2386–2388`, and non-`cfg(test)` callers at `:1734–1737` pass them. Consumption is test-gated, but this exceeds the contract’s `cfg(test)` instrumentation boundary. No changed solver decision was observed. Gate those parameters/calls or use an appropriately gated observation context.

The structural changes otherwise retain outer annotation and nested-row positions separately and traverse actual Function/Tuple source nodes. However, Rust `annotation_effect_sites` inventories explicit rows, including a possible root row; Lean `EffectVisit` models effect-port visitation. Their correspondence on the accepted fixture still needs authenticated extraction.

Run 2 reached solve/export/trace collection, then panicked before the newly added site, capture, delegated-tail and exported-port joins. The combined test runs owner observation first, so its delegation half did not execute. The original unequal test was not selected by either run. No native identity instance or unequal transport observation follows.

All five native falsifiers remain unexecuted for this changed observation: q substitution against fixed capture, identical wrong concrete sets, wrong owner wrapper, omitted origin, and swapped sibling ports. Current comparisons structurally address several of them but are not executed evidence.

## Lean audit

All ten theorem-type and transitive-axiom blocks for `YulangClosure.FormalPermissionSiteTraversal` were inspected:

| Theorem | Axioms |
|---|---|
| `visit_nonempty` | `propext` |
| `visit_lookup` | `propext` |
| `visit_unique` | `propext` |
| `leaf_has_no_visits` | none |
| `tuple_element_lookup` | `propext` |
| `associated_row_unique` | `propext` |
| `different_paths_distinct` | none |
| `associate_visit` | none |
| `identity_expected` | `propext`, `Quot.sound` |
| `identity_observations_decode` | `propext`, `Quot.sound` |

The modeled uniqueness statements are valid under their premises. `identity_expected` assumes representative identity and node lookup; `identity_observations_decode` assumes successful constructor decoding and exact agreement with the expected observation list. They do not prove HIR encoding, native snapshot authenticity, source recurrence or a source typing witness. The earlier failed `FormalPermissionSourceTransport.lean` remains unchanged, unaccepted and unimported.

## Authenticated hashes and execution

```text
Contract          712ba875f6f1d31fde5732aea7dc07b24769be77407590ac9ec4626c407e9f11
Rust handoff       2e2e643def9480470e84de6b0ae7e2b1021958bf2a28744b06f2422af677f428
Proof handoff      5e7950857877a92c90d871f9f98fd6c121b7feaf89b2910cf97aab4a9da55fa3
candidate_effect   92b8a6c59f1c052a47f12c8c858fa675eaddfa83d514f6ed3e2982bb88b1a182
candidate_scheme   31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707
Lean source        ac079ecc4c480adb4222723815b3f476469ed13b933c3994d090db0fae909207
restored old Rust  08760fd52e67d3b405638c8b378e98915ca903be7a96b4840aade071f5c2000f

Cargo 1 stdout+stderr a8329d2a9ed7bb9eac21b3d2288f0571c6565a61fdd746361a58a3f8916e966b
Cargo 1 status       39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c
Cargo 1 time         5a2d57d7b27dbe515f2a983721e6af1cc830dcbcf128bd5fb065eab6f6606e44
Cargo 2 stdout+stderr b567fa5d0be0227606a33b67c80790b3ea28a24f09591fa5da61bd8bb96e4053
Cargo 2 status       39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c
Cargo 2 time         601c5202c18136574ae122b83370d08aa51db50b0399b1741747ea1aaf328b87
Cargo 2 argv         bec8b193cbfe70693cee8ee7d69daecbd8a0a8aed781f2cbd4a357f76b21f2bc

Lean inventory       85c796552837b49be0109178cb2c7537bfff12fe49c220e757d7a3f657692dbb
Lean stdout          414a7c26cdc33fc3ecefda7303f2db517de65ef6273b2c621404cb4e176226bf
Lean stderr          e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
Lean status          9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa
Lean time            4a0b1a4ef40f745448e544f20197d8e84a20bb9c74726f9411f1fb3a4b862556
```

All dependency pins and the 280-entry Lean input inventory match. The two Cargo attempts each exited 101: first compile failure (34.47s, 1,159,624 KiB RSS); second selected test panic (42.75s, 1,669,792 KiB RSS); total Cargo wall 77.22s, zero swaps. Cargo logs combine stdout and stderr rather than separate streams. Lean passed on Lean 4.35.0 (11.56s, 970,168 KiB RSS, zero swaps). All stated process/RSS limits were met.

Original parent/source-native/A/B/effect-hygiene/principality/termination/production gates remain OPEN. The checked conditional traversal may be retained separately; the Rust overlay is not accepted until the four findings are repaired and freshly reviewed. The prior-handoff hash verifies restored bytes, not the duration of the wrong-path access.
