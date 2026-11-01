# R177 pin correction — independent review adjudication

Fresh independent review of the R177 malformed-pin incident returned INCOMPLETE. Strict enumeration found 31 direct-input paths: 30 valid 64-hex digests match; `candidate_scheme.rs` is the one malformed row (63 hex characters), with corrected current SHA-256 `6072c73bc1a1629f025dcaf61fcbed98c738d93f8993bd81182a391d1ad4d89e`. All four frozen artifact hashes in correction r1 match.

The blanket “all 30” statements are invalidated across the source handoff, proof handoff and activation receipt. In addition to source-handoff lines 74–84, proof-handoff lines 88–91 make candidate-scheme-dependent owner/occurrence/context/receiver and dormant-template claims. The proof author did not directly read this Rust file, but that does not authenticate inherited claims. These details are withdrawn pending correction-specific authentication. The earlier independent review's blanket hash confirmation and “no contract violation” conclusion are invalid to this extent.

Under the corrected actual file hash, the reviewer re-inspected `candidate_scheme.rs:1003–1063` as new correction-only evidence and confirmed its active-selection details; this does not retroactively authorize R177 reads. No other listed direct-input digest mismatch was found.

The original-App blocker remains independently authenticated by the pinned `shadow_apply.rs:4302–4402`, `OriginalSourceGeneration.lean:111–123`, `OriginalSourceChecking.lean:957–974`, and `Contracts.lean:127–130`: native Function demand exists, while original admission/checking extraction still requires a source Build premise. This is a missing proof bridge, not an implementation defect or accepted-source counterexample. R177 remains INCOMPLETE and `InferenceSoundness` remains OPEN with its original domain and shared witness.

No semantic decision or expected-output change is involved. Reviewer STOPPED after read-only audit; no writes, tests, builds, Lean, Git, or quarantined-path access.
