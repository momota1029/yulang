# SOURCE-RECEIPT-ORIGIN/r11 outcome

Disposition: **CLOSED_INCOMPLETE — diagnostic instrumentation accepted; complete source/native attribution remains underdetermined.** The first Rust producer and local invariant are localized. No semantic repair, source-qualified counterexample, source/native bridge, parent theorem closure or production promotion follows.

## Frozen admission and candidate

- Contract SHA-256: `3d7c9f3362f34277b446e0c3f52d05640a4afd3b866987501746a788e4c05aed`.
- Input manifest SHA-256: `a3b10055f0fb497bd341bdbd6ff7dc80d9ec40d15f564c6339d34e95539790b4`; 90 entries, 90 unique paths, 0 mismatches at admission. Reviewer authenticated the 87 immutable entries and verified the three mutable source outputs separately.
- Rust source: candidate_scheme `784b3087c875cc3bc05d16c50201d5efdb0da0425b7464ce8ff3744e1e93dfff`; candidate_context `be1be2277d54288ba4ae542e003dabc294031c29cb26b2b5d0454b0d1c102bd0`; candidate_extrusion `a6538ab3deae503fd2c002c88fb673a51848a350b226b8a38c3b43496cdd03ee`.
- Rust handoff SHA-256: `3cb334f2c151fea76072bb8789a88584e9009e248c03d4c7a180d818043f1f07`.
- Proof/source handoff SHA-256: `32bf2a5c6bb6ceab4fee82d7b53276c069e0a57e83f1d57132d64954606833be`. No Lean artifact was warranted or produced.
- Review receipt: `tasks/agent-loop/inbox/source-receipt-origin-r11-review.md`.

The instrumentation is test-gated and invocation-scoped. It records producer file/line for `ReceiptMismatch` while retaining the same error value and path; the fixed fixture and assertions are unchanged. Reviewer found no correctness issue in this diagnostic diff. No compiler/build/test/formatter check ran before review acceptance.

## Exact trace and execution

The single authorized Cargo attempt ran the unchanged focused test against the R11 workspace copy. It exited 101 after **95.0866s**, sampled CPU 47.00s, sampled process-group RSS **1,815,572,480 bytes** against 2,147,483,648, CPU affinity 0. It stayed within limits. Exactly one test ran and failed with the same `ReceiptMismatch`; no restoration or later cross-route authentication assertion was reached. Cargo-2 **NOT_RUN**; a second attempt is not justified.

The authenticated trace for invocation 1 records:

1. Producer `candidate_scheme.rs:4550`, inside `prepare_candidate_fresh_use` (`:4231`): processing a bound relation with `Some(ScopedDemand)`, `graph.negative_formal_roots.get(&demand.root)` returns `None`.
2. Consumer for the same invocation: the exact fixture's `session.execute()` returns `Err(ReceiptMismatch)`; the original unwrap panics at R11 `candidate_scheme.rs:8035`.

This matches the candidate consumer guard at immutable R9 `candidate_scheme.rs:4542`. The local invariant is now clear: every retained deferred-demand root consumed by FreshUse needs a corresponding captured reconstruction node. The capture owner builds `negative_formal_roots` from `formal_domains` (`:2815–2826`), while latent demand discovery separately interns demand roots (`:2709–2711`). Their coverage relation is the next ownership seam.

The trace omits the exact source occurrence, captured graph, bound/relation, demand root, source/use identities and antecedent. It therefore does not explain why this root is missing or establish the corresponding source judgment. Full source/native attribution remains UNDERDETERMINED; the `ReceiptMismatch` is not a source-qualified counterexample.

Cargo log SHA-256: argv `42022bbc16c6264b372f8b640c90488bfd19595571f623c650f5ff2121d06266`; stdout `3b05d5cc50b8ea3649a0b43f98ef1aeaa47026f936a90c3eaf251e40c3be3928`; stderr `34964b8c82e3ce9ec770a1c0e18d08ad2234ee3327064c36f3edb13530450fbf`; resources `1c66c6edcf99edc6df1b177cd3117b41ebf67cea2b243b27e26c4f80c5a16443`.

R11 Lean **NOT_RUN**. The cloned workspace contains inherited Lean-1 files; they remain R9 evidence and are not new R11 checks. The proof/source handoff reports no existing source law or accepted Lean theorem that establishes this native receipt bridge.

## Review, resources, and remaining gates

The independent reviewer authenticated all 87 unchanged pins, the three exact mutable source hashes, both handoffs and all four Cargo logs. Initial source-first ACCEPT preceded Cargo-1. Final review ACCEPTED the frozen diagnostic submission and logs; no BLOCKING, major or minor finding against the instrumentation.

Original `YulangClosure.SourceProblem.InferenceSoundness`, native/source correspondence, effect hygiene and production remain **OPEN**. The next bounded inquiry is the coverage correspondence between latent demand-root discovery and `formal_domains` capture, joined to actual source/use identities and antecedent. Any semantic fix needs its own precise authorization after that invariant and owner are established.
