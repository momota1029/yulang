# Cycle37: recursive structural refutation

Partial goal: extend outer-head contradictions through pair components, function argument/result variance, and equal-label variant payloads, then use these finite certificates in actual path-filtered self-output search. This is not complete satisfiability.

Data: actual TyTerm pairs; recursive checker descends into structural children with an internal decreasing measure. Independent Refutes has outer mismatch and structural inversion constructors. For every assignment, Refutes l r implies not Subtype(eval l,eval r). Pair payloads are covariant, arrow inputs contravariant and outputs covariant, variant payloads covariant; reuse Common inversion theorems rather than changing semantics. Effect rows are not inspected.

For every finite slot universe n and actual atom list, find direct refutation or lower/upper refutation joined by an independently defined directed Path. The executable check is equivalent to those certificates. Removing certificate-positive states preserves the full union of output models. The final inference adapter uses the existing directed Stable model iff.

Limits: records, effect-row contradictions, union/intersection internals, general satisfiability, existence, language classification, source/receiver generation and feedback termination remain open. General B4 still has five unfinished bridges.
