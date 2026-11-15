# Cycle204: I36 default-aware evidence successor

Status: implementation design, authorized by I36. Integration base 6237be0aa.

Replace only the source evidence judgment, retaining checked declaration, exact
canonical children, completed inspection, metadata and model constraints. Record
whether each requested associated body is explicit or default; use the existing
total-expression interpretation, not the old partial expression interpreter.
The new judgment must not mention classifier or execution evidence.

Build an evidence-only replacement of the Alloc V7 boundary. Prove its Local,
Reachable, Step, Stable, Models and operational/order bridges unchanged for any
replacement evidence. Then instantiate the replacement with the new judgment.
The final composition still requires the exact selected-node and generated-child
fields until actually proved; transport alone is not I36 completion.

Regression goals: explicit body, positional default, explicit override, cycle202
default source dictionary, and cycle199 output-conflict rejection. Do not claim
an all-source EvidenceNode from only these examples. Preserve old evidence and
counterexamples unchanged. Root Audit and README remain frozen.
