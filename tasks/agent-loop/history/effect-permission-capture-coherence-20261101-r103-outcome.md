# R103 outcome

Status: `ADMITTED`; implementation, proof, independent review, and exact gates pending.

Contract: `tasks/agent-loop/sprints/effect-permission-capture-coherence-20261101-r103.md`.
Admission: `tasks/agent-loop/history/effect-permission-capture-coherence-20261101-r103-admission.md`.

No theorem, source/native, semantic, production, or Rust integration gate is closed by admission.

## Rust lane adjudication — review completed, no source integration

The Rust author stopped with the R102 focused Cargo allowance unused. Fresh independent compiler-referee review matched all frozen hashes and returned **REJECT for source integration**. The bounded invocation was described as safe but limited; I did not spend it because R103's missing-source-evidence stop condition applies and the fixed outcome cannot be established by this candidate.

The sole code change in this lane normalizes decimal `TermArenaBrand(...)` values in the memo observer comparison. Review accepts that scoped comparison repair: independently created `TermBuilder`s use fresh arena brands, while the test retains term indices and the rest of its selected debug structure. It has not been executed and does not prove full solver-state equivalence.

Four protected R102 failures remain unresolved: shared-tail error source/action identity; unequal `r != q` transport; consumer return/provider path; and positive Support lineage through fresh-use. The candidate leaves `candidate_scheme.rs` unchanged. Independent review also found `intern_shape` canonicalizes a raw endpoint before `intern` receives it, so the current observer may lose the raw origin and its witness precisely on an unequal transport. The test must not be weakened or the merge fabricated.

Review corrected two handoff claims: the shared-tail assertion follows the late `E` contribution and `constrain_live_effect`, so logs do not distinguish an earlier root error from rejection of that contribution; and a failed `.all(...)` proves at least one route lacks Support, not that every route does. The original r1 handoff remains frozen as reviewed evidence; these corrections and the exact next source owners belong in a successor packet.

No Cargo invocation, Rust integration, theorem closure, source/native correspondence, semantic approval, or production gate is claimed. The Lean proof lane remains active under R103.
