# Independent review: formal permission projection r6

Reviewer: `/root/formal_permission_projection_r6_review`, fresh non-author `compiler_referee`.
Record provenance: the reviewer returned the following disposition in its final
message and STOPPED without writing because its role is read-only. Luna records
the response here verbatim in substance; this file is not reviewer-authored.

**Verdict: ACCEPT as conditional, incomplete static source evidence.** No
BLOCKING, major or minor finding against r6's qualified claims. The review
concerns lifecycle ownership/disposal and proposes no downstream symptom repair.

## Claim support

- Production source scheduling at `candidate_source.rs:1283–1340,2354–2380,
  2430–2463` connects lambda collection to formal publishers and `FormalEntry`.
  The source frame itself supplies no outer intrusion undo. “Production” here
  means reachable non-test candidate code, not production readiness.
- Private failed-attempt disposal at `lib.rs:10637–10680,17069–17079` and
  `shadow_apply.rs:1833,1890–1933` propagates errors before constructing a
  solved owner, consistent with authoritative inference principles §§4–5.
- Both rollback exits `lib.rs:9684,9702` happen after store and intrusion/domain
  cleanup but before complete row restoration. `:9535` propagates either
  error. Incoming routing (`:19025–19058`), local routing
  (`candidate_scheme.rs:4966–4976`) and source dispatch preserve failure; no
  error-to-success conversion was found on the inspected paths.
- `candidate_scheme.rs:2263–2285` and `lib.rs:10435–10440` support the bounded
  fresh-graph initialization claim, not transitive identity across unadmitted
  callbacks.
- Capture/export ownership is located at `candidate_scheme.rs:2787–2799,
  2824–2827,2892–2951`, `lib.rs:20058–20064`, and
  `shadow_apply.rs:2029–2054,2643–2665`. This does not prove preservation of
  the original captured image.

## Remaining premises

The next identified unadmitted callback owner is
`crates/yu-solver/src/candidate_receiver.rs`, reached from
`candidate_scheme.rs:3530,3541` and sibling shape queries. It must establish
that invoked operations preserve private graph/domain/term-store identity, or
fail without exporting a solved owner. The file was not opened or hashed.

C still requires the originating domain/path-to-original-capture-image equation
through canonicalization. D still requires successful shape/path correspondence.
B/C/D, the original endpoint-image obligation, parent A/B, full inference/
executor soundness, native correspondence, and production remain OPEN. R1 Lean
verification remains unchecked. No successful out-of-image endpoint
counterexample was established.

## Authentication and execution

Authenticated r6 contract `63c7079d33b639e43792a69f543f79eea1c1d9ef5cffce1f6126a4a392c28620`, handoff `013821988ef1979b5c530754a8f6c36a440c10ce6c5597fd3e64d1a0cfef749d`, all nine admitted source/policy pins, and r5 contract/handoff/review pins. All matched. Baseline Git identity was supplied rather than independently resolved.

Relevant embedded rollback/retry and consuming-failure tests were read, not run.
No tests/builds/probes, Cargo, Lean/Lake, Git, network, descendants or file
writes occurred in the review. Some combined reads were truncated; focused
reads covered dispatch, error, capture and export. **STOP.**
