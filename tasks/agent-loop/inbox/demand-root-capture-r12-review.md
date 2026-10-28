# DEMAND-ROOT-CAPTURE-CORRESPONDENCE/r12 review

Verdict: **CLOSED_INCOMPLETE. Retained Cargo-1 logs/resources are accepted; the executable instrumentation is rejected.** Cargo failed while compiling, so the fixture did not execute and no R12 trace or source/native conclusion was produced.

## Review stages

- Initial rev1 gate: **REJECT**. The FreshUse source occurrence lookup and `String` formatting ran before the active `r12_demand_trace` guard, contrary to the contract requirement that formatting/allocation remain dormant outside the exact trace scope. `graph.nodes.get(index)` was also mislabeled as a copied term.
- Rev2 gate: **ACCEPT for Cargo-1 only**. The lookup/formatting moved inside the lazy recorder closure, and the captured `Node` field label was corrected. No new source-first finding was reported. This acceptance did not authorize Cargo-2 or semantic repair.
- Final retained-log review: **CLOSED_INCOMPLETE**. The exact Cargo-1 invocation is authenticated and within resource limits; compilation errors invalidate executable instrumentation acceptance.

## Blocking findings

1. `candidate_scheme.rs:4642–4645` has six positional format placeholders but supplies five positional arguments. The `boundary={}` placeholder receives `graph.nodes.get(graph.root)`, causing the `Option<&Node>` Display error; `graph.boundary` is omitted. Fixing this requires a newly reviewed revision.
2. Adding `Graph::r12_trace_graph_id` breaks exhaustive test `Graph` initializers in immutable-under-R12 `shadow_apply.rs:4951` and `:5064`, each with E0063. Closing this requires a reviewed design confined to the leased source or a separately authorized lease change for those constructors.

No semantic repair, fixture/assertion/error/control-flow change, test result, source-qualified counterexample, or parent closure follows. Cargo-2 was **NOT_RUN** because its semantic-repair premise was not established. Lean was **NOT_RUN**; no theorem artifact was justified.

## Authentication and execution receipt

- Contract SHA-256: `6ec1f3ba7d3012c8ea29f53abe5b37cca26832d25319502bd472ec47132a0347`
- Input manifest SHA-256: `996d23a3f86541608bc7967658ceee9e29b128a95153fe6a60c26a00ef2ee05b`; 103 immutable entries authenticated with zero mismatches before and after review.
- Candidate rev2: `e6dc4f85c6b02278ea57ec82664ec4540db975c76046457e0b2d488f76cd37da`
- Rust handoff rev2: `9362f5698af63ea336603fc8f56c22e06353758c7bfdc4b415f4eefaf8c7f56e`
- Proof handoff: `98ac396943fdbc142336107f1602c084dfb6cd132c6f504d249132a0f7d60fac`
- Cargo argv: `16fb21db4f6a4147c75c1e7a335022b7195cec18e8856a0c1e5fe30f665b1450`
- Cargo stdout: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- Cargo stderr: `adc01deff4162f7840d4d43ba1e198de5510bb6b6ccfa924bad17b3b681f5237`
- Cargo resources: `b423da3769cb865df402107c1e0c97154fda2b86c6bdac40fa12d3fa311eb1bf`

The exact contracted Cargo-1 command ran once. Exit **101**, wall **63.4028 s**, sampled CPU **18.38 s**, sampled process-group RSS **1,208,184,832 bytes** of 2,147,483,648, CPU affinity **0**. Stdout was empty. Stderr records the format argument/type errors and both missing-field errors. No test executed.

Reviewer `/root/demand_root_capture_r12_review` remained read-only. Rev2 review observations spanned 6.9 seconds; final log-review observations spanned 13.6 seconds. Reviewer CPU/RSS and full launch-to-stop duration were not independently sampled. No review checks, retries, edits, Git, or descendants occurred.

Original `YulangClosure.SourceProblem.InferenceSoundness`, source/native correspondence, effect hygiene and production remain **OPEN**. The R12 trace did not establish why the same-capture root lacks published reconstruction or whether source authority permits a repair.
