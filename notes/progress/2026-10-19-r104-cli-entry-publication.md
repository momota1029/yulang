# R104 closeout: CLI publication stopped at source identity

Status: **FAILED_TO_ACHIEVE CONTRACT PREREQUISITE; command NOT RUN**.

R104 rev2 fixed two exact R97 source cells and proposed one serial public CLI test: the Value-role argument should publish an unhandled-request failure with empty stdout, and the `[] int` Computation argument should complete with `9\n`. Proof and implementation outputs froze, and all 14 declared input pins matched.

The fresh post-output specification review found that both frozen example files contain a terminal LF while the exact R97 source string literals do not. The implementation handoff also claimed a trailing-file-newline convention that R104 never authorized. R104's stop conditions explicitly require stopping on a source identity mismatch. The command gate is therefore not CLEAN and Luna did not run the test. The post-output compiler/source review was stopped after this decisive contract failure.

No compiler defect or runtime mismatch was observed. The predicted CLI outcomes remain predictions. No output was repaired under the frozen contract.

Frozen candidate artifacts:

- Contract rev2: `tasks/agent-loop/sprints/cli-entry-publication-20261019-r104.md`, SHA-256 `8cd15a5ab18a3923399ce2f14415df2782b131e626a7937b1e926decc8d40a61`
- Rev1 archive: `tasks/agent-loop/sprints/cli-entry-publication-20261019-r104-rev1.md`, SHA-256 `9e11dcf9fd1ec8ebdbaed38ad6c8a731af551fa3ffda28f45029a6205180b2cd`
- Proof: `notes/theory/2026-10-19-r104-cli-entry-publication.md`, SHA-256 `36e27caad8041a7ed423a36a07e58a78d15c482a35ec254036c416e72144f199`
- Proof handoff: `tasks/agent-loop/inbox/20261019-r104-proof.md`, SHA-256 `6dc4a08f608f572d239420f18f8342be6d36fac8695730a70b835b004d06bdca`
- Value-role example: `tools/inference-playground/examples/entry-unmatched-request.yu`, SHA-256 `5f0be9e24fc1aa885edd707da38aaa44057a0466960fbb76784cb28e622c1954`
- Computation-role example: `tools/inference-playground/examples/entry-computation-argument.yu`, SHA-256 `a81a52d582067e9d76ca41bfb946cd539cd98cc369b9b2c2a01fb0b3e0e239fd`
- CLI test: `tools/inference-playground/tests/cli_entry_publication.rs`, SHA-256 `ac2ba1cb201f35c79dbc67d140012b2c5db4b43c2395efe804be7e9a11f9535e`
- Implementation handoff: `tasks/agent-loop/inbox/20261019-r104-implementation.md`, SHA-256 `bd59897360484f2df1a3cdb789a6b1647f0f93e62cb6c4a5d0653dce5b8cd7dc`

R104's finite outcome/publication idea may be reconsidered only under new versioned authority, with source bytes and provenance stated exactly. The six effect-hygiene fronts, method/role proof, ordinary/effectful runnable source breadth, original Simple-sub/evaluator claims, semantic adoption and production authority remain open.
