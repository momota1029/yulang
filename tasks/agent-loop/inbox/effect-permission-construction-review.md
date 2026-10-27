# EFFECT-PERMISSION-CAPTURE independent review

**Primary transcription of the read-only compiler-referee messages.** The
registered `compiler_referee` role prohibited file edits, so the reviewer
returned its report directly to Luna. Luna records the independent message here
without changing its findings. Reviewer: `/root/effect_permission_capture_review`.
Sprint: `EFFECT-PERMISSION-CAPTURE-20261028/r1`, contract SHA-256
`5150233fa70a25ab5afb960a00bc18620bc645f030026dc19a1a1a9168daa93a`.
Initial report returned 2026-10-27 23:37:11 UTC after a launch recorded at
23:36:04 UTC. Review was read-only; no descendants, files, Git, Lean/Cargo or
network. RSS was not measured. A later resource/test addendum is appended below.

## Initial verdict

**CONDITIONAL ACCEPT** of the finite Lean model; **INCOMPLETE** for actual
Rust construction/capture correspondence and the required focused execution.
No production approval.

### Blocking source-correspondence boundary

Locations: `FormalPermissionCaptureConstruction.lean:47–57,89–128,175–191,
256–285,323–341`; `candidate_effect.rs:1414–1544,1658–1698`;
`candidate_scheme.rs:1713–1722,2670–2703,2784–2799`.

`constructor_to_export` proves the computed image in a catalog generated from
an already supplied `Shape`, under `Origin`. The delivered proof does not derive
that `Shape` or an `Origin` derivation from the recursive Rust constructor and
capture worklist. The separate `allocate` primitive is not used by `Shape`
construction. Live capture canonicalizes endpoint keys, assigns indices on
discovery and drains a LIFO worklist interleaved with row/bound/evidence
discovery. The model structurally enumerates both polar sides. Its
`publishedRoot` provides a composite catalog root; Rust publishes only if the
root endpoint already reached `capture.endpoints`.

A retained permission whose formal root has not arrived causes Rust to omit
`negative_formal_roots`, then export returns `ArtifactMismatch`. The model's
root theorem does not exclude this path. Different raw rows merging to one
canonical representative are also outside `shared_endpoint_image`, whose
hypothesis is literal key equality. `export_metadata` copies supplied metadata;
it does not prove authenticity against Rust producer records. List results do
preserve order and duplicates.

Minimum next proof: derive `Origin` and metadata authenticity from each
successful retained Rust construction, then prove live capture simulation up to
index renaming and canonical row representatives, including endpoint arrival,
index stability and negative-formal-root publication. Keep
`FORMAL-PERMISSION-LIVE-CAPTURE-1` and every dependent parent gate OPEN. This is
an incomplete contract result, not an unconditional theorem claim.

### Rust refactor and initial test status

Locations: `shadow_apply.rs:2607–2641,2680–2715`; existing tests
`candidate_effect.rs:2838,3442`; feature definition `crates/yu-solver/Cargo.toml:8`.

The diff is a literal extraction of the existing traversal. Static inspection
found the same owner filtering, empty-path rejection before domain/root lookup,
path allocation after root lookup, tuple bounds, checked offset addition,
terminal-Element rejection, Function child/effect positions, terminal Effect
row validation, metadata references, permission order and duplicate records.
The helper's extra empty-path check is unreachable after the unchanged caller
check. No changed success/error result was found by inspection. This was static
evidence, not execution evidence.

The first Cargo invocation exited 101 during test compilation because it
omitted `shadow-apply-candidate`; **zero tests executed**. This did not meet the
contract's focused regression requirement. The reviewer requested a separately
authorized corrected invocation and did not run any build or test. Its result
was not known in this initial report.

### Lean checker and axiom audit

The reviewer authenticated all 27 scratch manifest entries with no mismatch.
All 16 type/axiom blocks in `verification.log` matched the proof handoff. The
recorded checker used Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; version checks, explicit module
build and audit exited 0. Elapsed 4.221872s; maximum RSS 969156 KiB. The
reviewer ran no checker. The module imports only `Std`; no root/default-target
integration is claimed.

Axiom inventory:

- `allocation_shared`: none.
- `origin_nonempty`: `propext`.
- `catalog_root`, `catalog_argument`, `catalog_result`, `catalog_element`:
  `propext`, `Quot.sound`.
- `mem_intern`, `mem_internAll`, `mem_captureKeys`, `nodes_image`,
  `origin_image`, `constructor_to_export`, `shared_endpoint_image`,
  `export_metadata`, `constructor_list_export`, `constructor_list_metadata`:
  `propext`, `Classical.choice`, `Quot.sound`.

No `sorryAx`, project axiom or checker bypass was found.

### Authenticated pins

| Input | SHA-256 |
|---|---|
| Base contract | `5150233fa70a25ab5afb960a00bc18620bc645f030026dc19a1a1a9168daa93a` |
| Lean artifact | `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c` |
| Lean handoff | `eaac7c2db38ef17493ae5cf8a5cd8e6733f063176aafbdef543ab214e5f87331` |
| Rust artifact | `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d` |
| Rust handoff | `5c1bad68921ad95e3707ca90f4a9e559d01f385771ceacbe3f72829b3c2e7189` |
| `candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| Playground `scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| Lean verification log | `08d3ca779f7a7bcc55a552f48faba4e09643d5fa77e28be9df41efe29ca06672` |
| Lean verification JSON | `e1664f47c1c7429edc70bdd9b6932477a660a34d69359f9986ad658bc9564010` |

Read-only Git blob authentication confirms baseline `233b221d6` has pre-edit
`shadow_apply.rs` hash
`f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d`, and
reviewed commit `81fb62297` has the frozen refactor hash above.

All original A/B, effect hygiene/subtraction, complete Call, soundness,
principality, progress/termination, source/native and production gates remain
OPEN.

## Independent addendum: corrected Rust invocation and resource cap

The following is a primary transcription of the reviewer's read-only addendum,
returned 2026-10-27 23:40 UTC after inspecting the immutable retry receipt and
amendment 01. Reviewer identity remains
`/root/effect_permission_capture_review`; no build/test/Git, edit or descendant
was used.

**Accept the two focused test results as bounded execution evidence;
contractual verification remains INCOMPLETE because the invocation exceeded
its memory cap. No further retry.**

The reviewer authenticated retry receipt SHA-256
`dcb447df185e2366ea67c65eb4208df16b55d8c7e72f3663d6ca371d5e3a0b5a` and
amendment 01 SHA-256
`35e1a4e9f9859886fd7324abca59089da7f5e2c7d71c0fe12b544c396d4d13d9`. The
frozen Rust source and lane handoff still match SHA-256
`2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d` and
`5c1bad68921ad95e3707ca90f4a9e559d01f385771ceacbe3f72829b3c2e7189`.

The command, status, timing and output files agree on the exact invocation,
which exited **0** in **41.22 seconds**. Two tests passed and 814 were filtered
out:

```text
timeout 240s taskset -c 0 env CARGO_TARGET_DIR=/tmp/yulang-effect-permission-capture-20261028-r1/rust-target CARGO_BUILD_JOBS=1 cargo test -p yu-solver --lib --features shadow-apply-candidate formal_permission -- --nocapture
```

- `candidate_effect::tests::negative_concrete_formal_permission_recovers_its_shared_port_and_rolls_back`
- `candidate_effect::tests::tuple_formal_permissions_keep_element_paths_and_transaction_ownership`

**Major — resource requirement unmet.** Maximum RSS was **1,652,828 KiB**,
exceeding amendment 01's 1,048,576 KiB cap by 604,252 KiB. Amendment 01
requires INCOMPLETE on resource failure. Passing tests do not close that
requirement. Preserve the breach and stop; no further invocation is authorized.

**Minor — first-attempt evidence locator correction.** The retry receipt
initially said that the Rust lane handoff held the first failed command. That
handoff predates execution and says no build/test was run. Amendment 01 records
the first argv, exit 101, omitted feature and zero tests; no raw first-attempt
failure log was retained or authenticated. The retry receipt was corrected to
name amendment 01 as the evidence source and state this log limitation. The
reviewer did not authenticate a raw first-attempt log in the inspected scratch
files.

The actual constructor/`Origin`, live LIFO capture, canonical-representative
transport and negative-root arrival correspondence remain OPEN. Every original
parent and production gate remains OPEN. The addendum used read-only file
inspection and hashing only. **STOP.**
