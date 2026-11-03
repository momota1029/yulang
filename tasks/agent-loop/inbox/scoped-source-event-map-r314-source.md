# R314 source-owned event map — native producer handoff revision 4

Sprint contract: `tasks/agent-loop/sprints/scoped-source-event-map-r314.md`,
SHA-256 `e1a00225e89730efb4617efb5d3f584d0e45e0659df2f6f6cfcc73c8ef01fb0c`.
Baseline `b7c1dd2e1`; assignment `R314-NATIVE-SOURCE-EXPORT`; unchanged R159
parent gate. Requested model/effort Luna/high; observed model/effort and exact
active seconds UNKNOWN. No descendants.

## R4 outcome

R4 supersedes R3. The R3 handoff and module are preserved at
`/tmp/yulang-r314-native/r3-handoff.md` (SHA-256
`f700801aec6a1524a23022dbe1ae361dbefa7aba4f3db7179e7bde00d4b06ae9`) and
`/tmp/yulang-r314-native/source-event-map-r3.lean` (SHA-256
`8b3bb43a7211a836567011767c2742e52bd4b89e0d864e8d71e5e90e1d142771`). R2 and
R1 handoffs are likewise preserved in this scratch directory.

R4 completes environment binder identity in the test-only Lean exporter.
`RuntimeEnvironment` now contains the exact binder owner as a typed
`SourceRootIdentity`, in addition to binder kind, owner-local binder ordinal,
and captured cell index. Definition roots carry actual binding name, module
realm/path, and same-name ordinal; expression roots carry the actual HIR
occurrence; member roots carry module, member kind, and declaration/member
positions. The owner is derived from the retained `HirParameterId`, `HirLocalId`,
or catch binder's actual `SourceRootId`, and each root is authenticated against
the same retained HIR and parsed source.

The focused accepted-run test checks every bound ReturnSnapshot environment:
its emitted binder kind/id/cell/owner tuple must match the actual environment
and binder identity. It also confirms the snapshot contains ordinal-zero
parameters from distinct source roots, so `make` and `relay` parameter 0 do not
collapse to the same exported binder. R3's required-Annotation Ascription fix,
annotated source fixture, source/operand corruption checks, same-source/parse
checks, and same-HIR second-Machine rejection remain in place.

Residual limits remain explicit: no separately corrupted immutable HIR scope
tree test was constructed; wrong-snapshot rejection uses a second Machine with
its own missing/different Return snapshot rather than a hand-constructed copied
snapshot. Full dispatch-table replay is outside the lease; the authorized
`#[cfg(test)]` dispatch base/word readout and substitution id are retained.
Unsupported/unowned structures fail closed. No source structures are created
from runtime code.

## Artifacts and checks

Final leased repository SHA-256:

- `tools/inference-playground/src/runtime/program.rs` —
  `878530cb8934015e9e992c044ad2375ecc4903995db9a5d7df86caa36bc636f4`
- `tools/inference-playground/src/runtime/machine.rs` —
  `4095ebf6ee382cf14b283bbacb5cc2c03251e5e49f58d999ba84e2028b98de62`
- `tools/inference-playground/src/runtime/dispatch.rs` —
  `d99acad3e344bc06970faf0486ff7d10ba92bc7514cfb7eec58df8bbb28f6360`
- This handoff — hash reported to Luna after freeze.

Frozen R4 Lean artifact:
`/tmp/yulang-r314-native/source-event-map-r4.lean`, SHA-256
`b320d208d5fa2a2b84b29e74652e5529f0e78f35453e626733770b768a74df25`.
R3 annotated artifact remains preserved at
`/tmp/yulang-r314-native/ascription-r3.lean`, SHA-256
`f4d5b34d5025b68ed227bc28e6ae8ce71b69adaf7236a808b1b9c83b7cf262e6`.
Cargo used existing workspace `target/` as disposable generated scratch; it
was not manually cleaned.

Focused checks:

- `YULANG_R314_LEAN_WITNESS=/tmp/yulang-r314-native/source-event-map-r4.lean cargo test --locked --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib` — 1 passed. Exercises the exact binder-owner/id/cell assertions, source/export negative controls and same-run snapshot.
- `lake env lean /tmp/yulang-r314-native/source-event-map-r4.lean` — passed.
- `env -u YULANG_R314_LEAN_WITNESS cargo test --locked --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib` — 1 passed; no artifact file written.
- R3 annotated exporter fixture and both Lean parses passed before R4's schema-only addition; R4 retains its direct Annotation constructor and annotated fixture source.
- `git diff --check` on all four leased repository paths — passed.

No Git, network, semantic change, production API, or production behavior
change. All added producer code and artifact writing remain test-only and
opt-in.

## Correspondence and boundary

The module is finite evidence from the same accepted R313 parse/HIR/program/run.
It preserves complete selected source-root constructors, original binding and
formal resolution, scopes and positions, actual code instructions/children,
Request/Pending Callee/Return/Delay/Name/bind events, receiving values/views,
and the pre-Delay Return snapshot. Exact source text must equal retained parse
text. Foreign parse/HIR/run, unsupported structures, ambiguous joins, and
truncation fail closed. Session-local run ids and occurrence ordinals are not
cross-run identities.

R1's ad-hoc text, R2's missing binder cell, R3's missing binder SourceRootId,
and R2's invalid Ascription Option are superseded. Parent proof remains open;
this source producer does not certify its own correspondence. The proof lane
was notified and released its heavy checker before R4 Cargo execution. Proof
owner may consume only the R4 artifact hash above.

Sprint grant remains fixed at 1800 seconds; exact spent/remaining worker time
UNKNOWN. Cutover remains OPEN. Luna owns independent review and cleanup of
provisional test instrumentation. New repository paths remain the three Rust
files and this handoff. Generated scratch includes R4 Lean, preserved R1–R3
artifacts/handoffs, and workspace `target/`.
