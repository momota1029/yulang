# Structural closure capture allocation — cycle 2

Scope: the checked dual-inspection producer already defined in OpenProducer.
Not the state-narrowing/general source saturation graph.

Data: a nonempty finite Ty list computed from root endpoints, all Requests in
OpenFiniteClosure.closure, and both payloads of each actual production. A total
Ty -> Fin size lookup uses the first equal syntactic Ty; its default zero is only
observable outside this computed finite domain.

Execution: use this computed Allocation for the existing recursive pass.
Independent target: for every reachable request and its actual produced
(d,lo,up), decoding both allocated payloads recovers lo/up exactly. For every
interpretation Ty -> Comp, induced assignment evaluation preserves those same
payload meanings. Then the existing selected_prepare_exact statement can use
this actual allocator rather than an arbitrary caller function.

Boundary: equal syntax is not full graph/source-variable identity; unknown Ty
values can represent different unresolved source variables, so this restricted
allocator must not be presented as their general source allocator. No nominal
semantic interpretation is chosen or proved. Candidate narrowing can introduce
nodes outside this structural closure and remains outside this result.
