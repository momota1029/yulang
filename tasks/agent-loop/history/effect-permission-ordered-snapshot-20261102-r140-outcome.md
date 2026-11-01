# R140 outcome — ordered same-call permission snapshot candidate

Sprint: `EFFECT-PERMISSION-ORDERED-SNAPSHOT/20261102-R140`
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded` (`origin/yulang3`)
Contract: `tasks/agent-loop/sprints/effect-permission-ordered-snapshot-20261102-r140.md`, SHA-256 `e81ff2ddd7cda47bfb60bc1738e0c5bc3bfce4eb9effc183dd725003b4db06d0`.

## Reviewed bounded result

Fresh independent review PASSed the static research candidate with no required repairs: `tasks/agent-loop/history/effect-permission-ordered-snapshot-20261102-r140-review.md`, SHA-256 `d3a66d051dacb2cca835325adaf081865e08987fe253aed56d89f30f2c531624`.

The Rust handoff identifies one actual `candidate_formal_annotation` call, captures the permission-vector length in that session, and compares the same-call successful suffix against a source projection through one complete tagged `Eq` table. The pinned constructor stages local permissions and appends that vector in one ordered extension before its final fallible sample; only final `Ok` yields the candidate snapshot. The existing committed internal-producer fixture asserts the exact suffix paths AAR then RRR and pairs each row in order. This is static source evidence and an in-memory test-only candidate; no test was executed and no Rust source changed.

The matching Lean model states 25 table-local theorems over eight distinct tag shapes, including `FormalPosition`, exact recursive order/filter/path behavior, the AAR/RRR fixture, duplicate member preservation, separate root-entry shape and error-result exclusion. **Every target remains CONSTRUCTED_BUT_UNCHECKED:** the contract prohibited Lean execution, so actual theorem type output, transitive axiom lists and kernel acceptance are unavailable. No Rust execution or source-to-Lean identity equation was established.

## Boundaries and remaining premises

The review authenticated the frozen R140 contract and all three artifacts. Its source audit covered the exact constructor and fixture from immutable baseline blobs; packed parser/HIR blob IDs and sizes were separately authenticated by the primary. No accepted-source preflight runs in the chosen regression fixture; it is expressly internal-producer evidence and does not prove accepted-source uniqueness. `SourceNodeKey` equality is not treated as occurrence injectivity. Rust allocation abort is not mislabeled as a recoverable reservation error.

R140 establishes a reviewed candidate for the modeled same-call order/filter comparison only. The original `YulangClosure.SourceProblem.InferenceSoundness`, successful pinned elaboration and 25 type/axiom audits, concrete Rust-to-Lean table construction, FormalPosition-to-formal correspondence, all-source/native inventory equality, consumer/capture/copy/arrival/Catch correspondence, A/B, effect-hygiene H and production remain OPEN.

## Files and verification

- Rust source handoff, 28,566 bytes, SHA-256 `3335922fa8b259a1f4dea95bbf72e4ee6db8a99d7dd22fce25b3909e91aa8f56`.
- Lean module, 23,626 bytes, SHA-256 `da3baeabd61ff8fd30d078a4481f4a6c62ef5801cdb670f634e4d7c827add985`.
- Proof handoff, 21,870 bytes, SHA-256 `a0a8e21563435014b8da3c48bcae871ae87794e4f0ec68d842e243825364de05`.
- R139 identity-table review findings are carried forward; corrected R138 dependency digest is `2cfe94f5dd822c4df4619fa194186c2537393c1c3ed8340e244f56b6e93ac480`.
- `python3 tools/agent_sprint.py check`: static protocol check PASS. No compiler, Lean, build, test or Cargo command ran.

All authors and reviewer stopped writing. This is a research-only reviewed checkpoint, not implementation approval or theorem closure.
