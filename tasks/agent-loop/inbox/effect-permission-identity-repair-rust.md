# Rust handoff — EFFECT-PERMISSION-IDENTITY-REPAIR-20261028/r1

Assignment: `EFFECT-PERMISSION-IDENTITY-REPAIR-20261028/r1/rust`
Handoff revision: 1
Contract SHA-256: `2008579471df100926ca41be4cd6fac780a7c2cc53ae5f5b1555bdec50c19c39`
Contract baseline: `29b85224b` plus the admitted candidate overlay. The current
workspace HEAD observed at run preflight was
`3d8ac2d8771d6e3818c38d273d431311c178571f`; Luna confirmed this was current-state
receipt commits only and that the dependency pins remained unchanged.

## Result and parent application

Outcome class: **implementation, incomplete**. The feature-correct library test
build compiled successfully. Ordinary `CandidateInference::solve`, exact-owner
export and `formal_effect_permissions` returned in the first test before its
trace assertion failed; the symbolic test also solved/exported and returned a
nonempty graph before its source-site assertion failed. The intended source to
capture to exported-port identity assertions therefore did not pass. No test
passed, and no source/native theorem or parent gate closes.

The implementation adds only `#[cfg(test)]` trace identifiers/events, lazily
recording constructor permission-row allocation, source site/path, symbolic
effect memo miss/hit and delegation, canonical endpoint interning, capture ID,
owner capture and the exact exported effect-row node. It also initializes the
two required test-only `Graph.formal_capture_trace_id` fields in
`shadow_apply.rs`. No solver choice, source acceptance, recovery, API, language
semantics, expected output or production behavior changed.

The trace representation distinguishes the concrete permission row from a
symbolic memo row: each allocation has its own row witness, while the constructor
ID connects events within one annotation. The permission-row-to-owner-export
assertion was not reached. The symbolic memo/delegation-to-canonical-node
assertions were not reached. Neither relation is accepted from this run.

## Frozen inputs and changed paths

Pre-edit overlay pins checked at task entry:

- `candidate_effect.rs`: `f7dd1d1bf1e66e98d969aa9f7cadc1faad4c1325acf65e8d9da56e2593a84bec`
- `candidate_scheme.rs`: `0c3d87610452f78f27189d0f6554d52d9422e2fcc2a4d38d93014538002553a4`
- `shadow_apply.rs`: `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`
- `yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Final source hashes:

- `crates/yu-solver/src/candidate_effect.rs`:
  `85d624cd2a1c5b4f821b58aa30f4dbf4fb59c1f4c9650f88b51382c07cc95d3a`
- `crates/yu-solver/src/candidate_scheme.rs`:
  `9eaee3528f36fcac180fe3b0e0428c8f353c2911fb0b854e621e57e08720e4d7`
- `crates/yu-solver/src/shadow_apply.rs`:
  `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-solver/Cargo.toml` (unchanged):
  `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- This handoff: hash is supplied separately with the frozen submission.

New repository path: this handoff. Exact leased source paths are the three
listed above. No other repository path was written. New disposable scratch is
limited to `/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/`
(argv/input receipts, raw logs and generated Cargo target tree); primary owns
scratch cleanup.

## Sole released invocation

Frozen argv locator:
`/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/argv.txt`,
SHA-256 `5ac9f05783b1f35077b3382c3319eeff02c0db5d9605f1d1482aa9e7a010e316`.

Exact command, from `/home/momota1029/rust/yulang`:

```text
taskset -c 0 timeout 180s /usr/bin/time -v env CARGO_TARGET_DIR=/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target CARGO_BUILD_JOBS=1 cargo test -p yu-solver --lib --features shadow-apply-candidate formal_permission_constructor_ -- --nocapture
```

Luna released exactly one invocation after independently checking argv and
source/dependency hashes, the CPU 0 pin, no competing heavy process, and
23,137,632,256 bytes available memory. The task exited **101** after **65.83 s**
wall time, **58.91 s** user CPU, **4.61 s** system CPU, **96%** CPU, maximum RSS
**1,659,572 KiB**, and zero swaps. One CPU was pinned. The run was below the
180-second and 2-GiB limits. There was no retry.

The build compiled `yu-solver` with the required feature, then ran two selected
tests; **0 passed, 2 failed, 816 filtered out**:

- `formal_permission_constructor_owner_domain_graph_export_join` panicked at
  `candidate_effect.rs:2975`: no trace event matched the expected
  `constructor-formal-domain-publish` plus exact `owner` debug string.
- `formal_permission_constructor_symbolic_effect_memo_hit_miss_and_delegation`
  panicked at `candidate_effect.rs:3073`: no `formal-effect-site` event matched
  the expected constructor ID, owner debug string and `source_row=Some(...)`.

The assertions omitted the full in-test trace from panic output, so the exact
format/identity discrepancy is not established. Do not infer success of later
identity assertions from the compile or the returned candidate/export values.
`git diff --check` on the three leased source paths exited 0 before the run and
again after it.

Raw logs:

- stdout: `/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/stdout.raw`,
  SHA-256 `72744a0f9dc4f8c1bba006815ffd3b3a6b37f95a00b8851e75f3f78b1f8c0927`
- stderr, including compiler warnings and GNU time report:
  `/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/stderr.raw`,
  SHA-256 `a4c61c4db3ac87bd2c188fffbee787c34239a7e96c044802414ce53dc53f22c8`
- frozen input receipt:
  `/tmp/yulang-effect-permission-identity-repair-20261028-r1/rust-target/frozen-inputs.txt`,
  SHA-256 `e0efebf544e33291023269b36e47034e2f6eb030ca340ebe4446df54dd1768ca`

Assignment elapsed budget spent: 65.83 seconds of the 600-second Rust
allocation. The single-Cargo-invocation allowance is exhausted for this packet.

## Prior evidence reused or rejected

- Reused the prior ordinary-source tuple fixture and its finite expected paths.
  Earlier source-origin evidence reported three passing tests and owner export,
  but did not retain a raw Cargo transcript and its owner-port assertion relied
  on graph membership. It does not validate these stronger assertions.
- Rejected the earlier live-capture fixture as evidence for the allocated
  parameter row: it passed the unoffset parameter and captured the wrong row.
- Reused the exact checked 12-theorem `FormalPermissionSourceOrigin` result
  only as conditional proof evidence. The prior 11-declaration extension
  artifact failed before type/axiom audits; no Lean result is repaired here.
- The present run is compile evidence for these frozen source bytes and a
  negative test-assertion result. It supplies no authenticated successful
  same-witness source/native observation because both focused tests failed.

## Open premises and next related step

Parent `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3, 5 remains OPEN. The exact missing source-owner evidence is to capture
the actual emitted trace (or strengthen panic diagnostics within a newly
leased revision), reconcile the HIR source owner representation used by
constructor events with the owner key used by capture/export, then establish
the concrete allocated row's original occurrence/path, canonical Effect
endpoint/node, capture ID and exact exported permission port. Separately
establish symbolic memo/delegation row identity through its owner capture.
Falsifier: an ordinary source-approved export that assigns the witness row to a
different occurrence/path, capture, endpoint/node or owner port. The first
transition still unsupported is this exact source-owner/capture/export trace
join. The source/native universal bridge remains open.

Provisional boundary: the added instrumentation and tests are test-only,
dormant when disabled, and not accepted as a proof or cutover. Cleanup/retention
owner is Luna. No source-domain restriction, semantics, diagnostics, inference,
or output expectation changed. No independent reviewer has reviewed this
artifact; the author does not self-certify it.

Requested role/model/effort: `implementer`, `gpt-6-luna` / high. Observed model
and effort: **UNKNOWN** (no runtime metadata available to this worker); no
fallback is claimed. No descendants or external processes remain. Cargo ended
with exit 101 and all writes are frozen. Worker disposition: **STOPPED**.
