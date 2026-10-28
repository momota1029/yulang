# R19 independent review — INCOMPLETE

Session: `CALL-EFFECT-OWNER-REALIZATION-20261028/r19`
Reviewer: `/root/native_external_effect_frame_r8_review` (requested Sol/medium; observed model, effort, CPU/RSS and total elapsed runtime UNKNOWN).
Disposition: **INCOMPLETE; no ACCEPT. STOP received and obeyed.**

## Findings

### Major — observer is reachable outside tests and adds unbounded collection

`authenticate_demand_transport_observed` in the candidate `candidate_scheme.rs` and its wrapper are not `#[cfg(test)]`. Non-test observation APIs call the wrapper from `shadow_apply.rs` at lines 1694 and 1741. The new `collect::<Vec<_>>()` can therefore allocate on those public observation paths. The old selector retained one index and stopped after a second match; the candidate scans the full graph and stores all matches. For N nodes and M matching nodes, auxiliary storage changes from O(1) to O(M), duplicate rejection loses early termination, and allocation failure adds a failure boundary. This conflicts with the packet's test-only diagnostic restriction and the overlay/implementation claim that no production path changed. No fix is authorized by this review.

### Major — producer ownership remains unresolved

The Function arm of `mapped_endpoint_at` derives its endpoint solely from node polarity and `retained.terms[node]`. After filtering `Node::Function` and polarity, matching the constructed PositiveFunction/NegativeFunction endpoint is equivalent to the old polarity-plus-term predicate. The row map and effect-operand map do not participate. For two matching positive Function nodes, both versions reject; for zero matches, both reject; for one, both select the same node and proceed to the existing four typed-port checks. The edit improves cardinality observation but supplies no new typed producer ownership or constructor-to-consumer equation. Closure still requires actual construction-owned producer evidence and transport to the consumer, including all four ordered port equations.

### Exact diff review incomplete

The displayed overlay block occurs once in the candidate. Reversing that block in memory did not reproduce the pinned baseline hash; the result was `05eae01abfa22a2a8ce6f450419fa9a710fb506c27b64b0b275cd7febe97f477`. Surrounding changes may be omitted from the excerpt. STOP arrived before complete baseline/candidate diff validation. No exact one-hunk delta is certified, and other differences are not excluded by this review.

## Authentication and preserved pins

Of 727 original input pins, 726 matched. The sole mismatch is the separately admitted scheme overlay. All 11 parent pins matched. The original manifest authenticates baseline bytes, not the candidate. Amendment 02 records the primary sequencing error and separately pins the candidate. The source lane stopped before reading source bodies and completed no row join. Its malformed contract-hash transcription is corrected by amendment 02.

| Artifact | SHA-256 |
|---|---|
| Base contract | `9400d07a47cb48043983fa4ae43c41962a581a97a732d181c92cdd2a090e6bd7` |
| Amendment 01 | `9c90b318aaa322aade2440c9924a1e38d7d8e67b2e1e40fb27bd6c568904aa93` |
| Amendment 02 | `e40b7ec782dc9010e496e5293f916105c541ff50b4b30c2c818678a771a410bf` |
| Unchanged manifest | `f287059a08410cf644644be214ba622de92d3e2d10c4897441cbb360c91ca22d` |
| Candidate overlay 01 | `8292a917f07a2c2b509ed5875d734e193d6da798bff325a36015039da6da4e4a` |
| Candidate scheme baseline | `3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7` |
| Candidate scheme overlay | `985ea301fbca632ecabe494f4324326759477608c0bf1a81e297c9e8b41cd37c` |
| Astra note | `08d80e411cfd169dceaeaf36415c1bbed34f1c77eb6f1e62588f06d6647cbfa3` |
| Astra handoff | `26bef2e205b894467473bb3f6c95f6c1ef0316aa755e4d11eb4b3e11c883db60` |
| Lean handoff | `dd6883a4d8dc31f98938d0807a49396d8485c4c035d9120e3d579810c66a5735` |
| Source STOP receipt | `5708927ca95ab623979d3580704bd0b2be13a13fda07c324b74c45971252dd4c` |
| Implementation handoff | `3ada7346900ea9d013771e6eb864f3ffc845464bbf971116a6bd511aedee39a2` |

## Proof and gate disposition

The Astra obstruction and inspected Lean definitions preserve the original universal source claim and shared witness. `OriginalSourceGeneration.lean:111` generates Call atoms but does not construct their original semantic interpretation. `OriginalSourceInterpretation.lean:343` retains independent `actualTypedPath` and `actualContext` predicates. No new Lean module or checked theorem was delivered; theorem types and axiom audits are NOT_RUN.

Complete Call, independent F1/FK1, arbitrary lawful allocations, foreign continuations, source/native correspondence, effect hygiene, implementation and production remain OPEN. Close R19 **CLOSED_INCOMPLETE** under amendment 02. No Cargo, tests, builds, formatting, Lean, Git mutation or descendant dispatch occurred during this review. The reviewer performed no writes. First clock observation was `2026-10-28 13:49:12 UTC`; STOP timestamp was not independently sampled and was acknowledged immediately. No paths are released by this receipt.
