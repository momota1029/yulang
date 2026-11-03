# R341 — original use pullback and continuation boundary

Baseline `fb139be40`. `OriginalEIUsePullbackR341.lean` proves that R295's
declaration and use packets round-trip for every dependent use world without
an inverse or surjectivity assumption. Scope and shared-slot data are retained.
This structural result does not authenticate an actual source continuation or
derive the missing resumed callee evidence at R339/R306/R159.

Its initial abstract discriminator constructs a nonempty response and pointwise
request/resume primitive inputs while the resumed callee clause fails. The
independent reviewer found that its registry is chosen after the response, so
it does not establish the universal premise for one fixed registry. The result
is retained with that exact limitation, not as a source-qualified refutation.

`OriginalEIFixedRegistryR341.lean` addresses that quantifier issue with one
registry and resolution selected before all responses and a closed inhabited
model. It preserves responses at every event and every Nat value and satisfies
the original abstract universal primitive-input premises while the universal
callee-request conclusion fails. Independent review confirmed the implication
being refuted and found no empty response-domain loophole. This remains an
abstract interface model: the prior Return/reify inventory is vacuous and the
selected development relation uses one fixed raw continuation. It does not
model authentic source response/development coverage or refute adopted EI.
The original authenticated continuation, receiver projection, independent arm
licenses, Checking, admission and unchanged R159 proof remain open.

Independent pinned Lean 4.35 checking with `-j1 -M2048` compiled and audited
both frozen files, including all originating theorem types and axioms. Only
standard Lean axioms occur. First check receipt SHA-256:
`ed7489a11599850ec5b109c16ab1b41313709ca1178b0eb3af91c1353fc1c16e`.
Fixed-registry check receipt SHA-256:
`a6216d61e6cd624a6cd6f01ae84dfc058514703db54387c8ce01304aa219b2c2`.
