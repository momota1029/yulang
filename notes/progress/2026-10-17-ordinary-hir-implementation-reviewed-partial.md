# Ordinary HIR application implementation sprint closeout

Sprint `ordinary-hir-application-admission-implementation-20261017`, rev3,
closed `REVIEWED-PARTIAL` after an independent compiler review found one
BLOCKING ownership error and six major conformance/performance defects in the
frozen candidate. Candidate code remains preserved without tests, builds or
runtime evidence at commit `4f4dcb7b9`; review receipt is
`notes/progress/2026-10-17-ordinary-hir-applied-compiler-review.md`, SHA-256
`9f576d7f6362f87ae21d01d997dc7418c529aade689d7eafbd22d78b5cf239a6`.

The findings are: moved `causal_errors` reused on fallback; trailing-comma
CallTail admitted; retained error diagnostic ordering changed; binding
EvaluationClass computed from a temporary Error; source keys reconstructed by
range; repeated full-module root search creates quadratic work independent of
R; grouped fixture falsely expects unresolved operands to have no errors.
Exact repairs and falsifiers appear in the review receipt. No source behavior
was executed; original theorem gates closed: 0. The implementation author and
compiler reviewer STOPPED with no remaining leases.

Resource accounting: cap4020; charged2600; retired1420; no remainder. Retired
work consists of Astra unused270, unused pre-code review90, implementation
unused250, and the then-current sprint's unspent allocation810. No retired
budget is revived. The output-sensitive resource amendment remains adopted for
future in-scope implementations.

The replacement sprint focuses on repairing this exact candidate with a
proof/source provenance packet and narrow pre-code architect gate before any
compiler edits. Original claims and quantifiers remain unchanged.
