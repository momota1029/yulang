# Ordinary HIR repair solver vertical rerun

After the corrected HIR integration passed, Luna ran the held solver vertical
exactly once:

```text
timeout 45s cargo test -p yu-solver --features shadow-apply-candidate --test research_accepted_call_vertical
```

Exit 0 in 7.185s. The one test,
`accepted_source_generates_calls_propagates_and_reaches_fresh_uses`, passed
(1 passed, 0 failed). Compilation completed successfully. The output repeated
the three known `yu-hir` dead-code warnings for provenance payloads and
`replace_admission_root`; there were no test failures.

This executes the existing candidate vertical from accepted source through
constraint generation, propagation, and fresh uses. It establishes neither
the source/native correspondence of the original theorem nor Call,
F1/FK1, N-Transport, soundness, principality, termination, or production
conformance. Original theorem conditions closed: **0**.
