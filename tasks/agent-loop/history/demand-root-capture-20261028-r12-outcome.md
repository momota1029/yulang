# DEMAND-ROOT-CAPTURE-CORRESPONDENCE/r12 outcome

Disposition: **CLOSED_INCOMPLETE — source/proof correspondence remains unresolved, and the authorized diagnostic instrumentation did not compile.** No runtime trace, semantic repair, source-qualified counterexample, original theorem closure or production promotion follows.

## Admission and frozen outputs

- Contract SHA-256: `6ec1f3ba7d3012c8ea29f53abe5b37cca26832d25319502bd472ec47132a0347`.
- Input manifest SHA-256: `996d23a3f86541608bc7967658ceee9e29b128a95153fe6a60c26a00ef2ee05b`; 104 entries at admission. Reviewer authenticated all 103 immutable entries with zero mismatches; mutable candidate and handoffs were checked separately.
- Candidate `isolated/demand-root-capture-r12/crates/yu-solver/src/candidate_scheme.rs`, rev2 SHA-256 `e6dc4f85c6b02278ea57ec82664ec4540db975c76046457e0b2d488f76cd37da`.
- Rust handoff rev2 SHA-256 `9362f5698af63ea336603fc8f56c22e06353758c7bfdc4b415f4eefaf8c7f56e`.
- Proof/source handoff SHA-256 `98ac396943fdbc142336107f1602c084dfb6cd132c6f504d249132a0f7d60fac`; no Lean artifact was warranted.
- Review receipt: `tasks/agent-loop/inbox/demand-root-capture-r12-review.md`.

The candidate contains test-only invocation-scoped observations, no semantic repair. Rev2 moved FreshUse source lookup/formatting inside the active lazy trace closure and accurately names the captured `Node`. Fixture, assertions, error kind, and ordinary control flow were preserved. Initial rev1 was rejected for eager test-scope formatting/allocation and a mislabeled field; rev2 received source-first ACCEPT for Cargo-1 only.

The proof lane found that latent demand roots are interned separately, while capture publishes only roots represented in `formal_domains`; FreshUse requires every retained demand root in the reconstruction map. Exact source/use/antecedent correspondence and the source Call/shared-witness bridge remain open. That structural fact does not establish source authority for a semantic repair.

## Cargo-1 result

The exact contracted focused Cargo command ran once under CPU affinity 0 and the process-group resource monitor. Exit **101**, wall **63.4028 seconds**, sampled CPU **18.38 seconds**, sampled process-group RSS **1,208,184,832 bytes** against **2,147,483,648 bytes**. The 120-second wall limit and RSS limit were respected. Cargo 1.95.0; rustc 1.95.0.

Compilation stopped before the fixture ran:

1. At `candidate_scheme.rs:4642–4645`, six positional format placeholders have five arguments; `graph.boundary` is missing, and the owner-node option lands in a Display slot.
2. `Graph::r12_trace_graph_id` is missing from two exhaustive test initializers in `shadow_apply.rs:4951` and `:5064` (E0063). That file was outside the R12 write lease.

Cargo stdout is empty; complete stderr is preserved. Logs:

- argv `16fb21db4f6a4147c75c1e7a335022b7195cec18e8856a0c1e5fe30f665b1450`
- stdout `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- stderr `adc01deff4162f7840d4d43ba1e198de5510bb6b6ccfa924bad17b3b681f5237`
- resources `b423da3769cb865df402107c1e0c97154fda2b86c6bdac40fa12d3fa311eb1bf`

The independent reviewer accepted the retained command/log/resource evidence but rejected executable instrumentation. Cargo-2 is **NOT_RUN**: the sprint contract allows it only for a conditionally pre-authorized semantic repair, and no repair authority or candidate exists. Lean is **NOT_RUN** because no justified theorem artifact exists. No runtime `ReceiptMismatch`, root/source join or semantic conclusion was observed.

## Remaining gates

Original `YulangClosure.SourceProblem.InferenceSoundness`, source/native correspondence, effect hygiene, and production remain **OPEN**. A continuation needs a new exact packet to repair the test instrumentation compile issues, including either an approved lease to the two `Graph` initializers or an in-lease identity design; it must receive fresh source-first review before another Cargo attempt. The semantic root coverage law and source Call/shared-witness bridge remain separate open obligations.
