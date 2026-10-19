# R104 implementation handoff

Assignment: `R104-IMPL`, exact contract `tasks/agent-loop/sprints/cli-entry-publication-20261019-r104.md`, SHA-256 `8cd15a5ab18a3923399ce2f14415df2782b131e626a7937b1e926decc8d40a61`.

Status: FROZEN. The two exact source examples and one serial public-CLI integration test are present under the implementation lease. No production source or existing expectation was changed.

## Frozen outputs

| Path | SHA-256 | Change |
| --- | --- | --- |
| `tools/inference-playground/examples/entry-unmatched-request.yu` | `5f0be9e24fc1aa885edd707da38aaa44057a0466960fbb76784cb28e622c1954` | Exact Value-role `ignore x` cell from R97. |
| `tools/inference-playground/examples/entry-computation-argument.yu` | `a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd` | Exact `ignore (x:[] int)` Computation-role cell from R97. |
| `tools/inference-playground/tests/cli_entry_publication.rs` | `ac2ba1cb201f35c79dbc67d140012b2c5db4b43c2395efe804be7e9a11f9535e` | One test, `entry_role_controls_cli_publication`, invokes `CARGO_BIN_EXE_yu-playground` serially with `--run main --steps 1000` and each example path. |

The test checks that the Value-role run fails, publishes no stdout, and reports `unhandled runtime request` on stderr. It then checks that the Computation-role run succeeds with stdout exactly `9\n` and empty stderr. The checks observe only these two public CLI outcomes.

## Source and consumer correspondence

R97's pinned `runtime_control.rs::section21_outer_annotation_selects_entry_for_ignored_arguments` already prepares both exact `DECL`-prefixed cells through parse, LocalSource lowering, `CandidateInference::solve` with no conflicts, `RuntimeProgram::from_hir`, and machine start. Its machine assertions predict an unhandled request with Unit payload for the unannotated formal, and integer 9 for the `[] int` formal. R104 preserves those sources byte-for-byte apart from the contract's trailing file newline convention.

The pinned runtime consumer maps outer annotation-row presence to Computation role in `RuntimeProgram`; the machine enters the callee before forcing an argument for that role, while Value entry evaluates the argument first. The pinned public `execute` maps an unhandled request to the existing diagnostic and a completed integer to `9\n`. The pinned CLI opens the supplied file, prints output only after successful execution, and writes errors to stderr with failure status. The new test therefore connects the R97 source/runtime result to public CLI publication; it adds no constraints or semantics and makes no source/native theorem claim.

## Evidence and boundaries

- All 14 R104 rev2 frozen-input hashes matched the contract before edits.
- Inspected only those frozen inputs and the assigned output paths.
- No build, test, CLI/runtime execution, formatter, Git command, or production edit was performed. The one contracted integration command is reserved for Luna after both producer freezes and CLEAN independent reviews.
- No new source owner or missing dependency was encountered.
- Prior evidence reused: the exact R97 source cells, preparation, and machine outcome assertions. No withdrawn Simple-sub bypass was used.
- Unresolved: R104's one CLI integration test has not run; static/source inspection cannot establish observed publication. Parent Simple-sub/evaluator closure, semantic adoption, production authority, and the other hygiene fronts remain open as the contract states.
- Provisional boundary: this is finite CLI consumer evidence only; it does not establish general CLI soundness, general §21 behavior, unmatched suffix preservation, handler/continuation behavior, permission equivalence, method/role dispatch, or the parent theorem.

## Resource receipt and next step

- Requested assignment model/effort: Luna/high. Observed model/effort: UNKNOWN.
- Assignment cap: 360 seconds. Elapsed and remaining time: UNKNOWN.
- Exact checks performed: frozen-input SHA-256 comparison; output SHA-256 collection; read-only source inspection. No executable check was permitted in this lane.
- Next in-envelope step: Luna freezes the proof output, obtains fresh independent specification and compiler/source reviews, then may run the contract's single exact integration command once. No repair/retry is authorized on failure.
