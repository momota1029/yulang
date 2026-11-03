# R342 — source-projected higher-order continuation

Baseline `92a5212a0`. `OriginalSourceContinuationR342.lean`, SHA-256
`b54a3ccbe0f6152333eafad58cc8d8fdc48f07b3587ba5ae8b1cd8d21a46c34d`,
computes a HigherOrder projection of the canonical R315 `makeInitializer`,
preserving its returned identity lambda. It constructs an eight-step formal
request prefix and, for every represented typed response, the same saved suffix
and a three-step return. The canonical source is linked to R315's decoded
initializer and the primitive lookup is checked against the source table.

Independent source review confirmed these finite-model statements. The
projection is specific to the canonical initializer: primitive lookup uses
that fixed table even when the projection function is called on other syntax.
The model inserts a value-lambda wrapper and identity result adapter for the
operation; arbitrary receipt metadata and synthetic entry events have not
been proved to simulate the native request/owner behavior. Its typed responses
are embedded TypedCall responses, not every original semantic response.

The callable-valued result has no preimage under the old TypedCall type
embedding, and this module does not apply R336's Control consumer. It does not
prove original `Inputs`, source admission, checking, continuation, licensed
Union child, independent arms or unchanged R159. Earlier R342 owner
investigations found no existing original d_f Request/resume eliminator or
source-owned complete scoped ArmDecl→R293 catalogue construction; these are
bounded source-search results, not a claim of semantic impossibility.

Independent pinned Lean 4.35 verification at `-j1 -M2048` authenticated the
dependency/cache inputs, compiled the target and audited all 53 originating
constants including 16 theorems. Only standard Lean axioms occurred. Receipt
SHA-256:
`3f18a2df5b68b79c7dab714adef96bdc5a70ba8b2f00a191dc9d8a46aa60b456`.
