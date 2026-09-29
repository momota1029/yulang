# Intrusion structural-rule and implementation map

Date: 2026-09-30
Oracle: frozen Yulang2 `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: read-only source maps; no successor rule or API selected

## Oracle structural rules

The Oracle's Function subtyping path in
`crates/infer/src/constraints/machine/propagate.rs` reverses arguments and
argument effects, and preserves covariance for result effects and results
(roughly lines 212–270). A pure-argument-effect special path relates the upper
Function's argument effect to its result effect after stack adjustment. These
are finite polarized endpoints; effect variables use ordinary TypeVar bound
propagation. Effect-row upper bounds additionally pass through weighted row
filter/residual logic in `constraints/row_effect.rs`, outside the simple
variable-edge presentation.

Tuple subtyping propagates elements covariantly only when arities match
(`propagate.rs:317–329`). Arity mismatch does not emit a child constraint at
this stage; concrete specialization later rejects the mismatch
(`specialize2/type_graph.rs:731–759`). Therefore the inference closure alone
does not characterize the complete public success/failure behavior.

Record inference checks fields demanded by the upper endpoint. Matching fields
are covariant except that the inference path skips propagation for a lower
optional field against an upper required field; extra lower fields are
ignored (`propagate.rs:293–313, 550–663`). Missing upper fields likewise do not
fail in that step: concrete specialization rejects a missing required field
and accepts a missing optional field (`specialize2/type_graph.rs:760–796`).
The inspected specialization checks absence of required upper fields but does
not globally reject every present lower-optional/upper-required pair; an
optional upper field that is present can still get value comparison. Tail/head
spread rows add more behavior and are outside the closed-record witnesses.

Same-path, same-arity nominal constructors compare arguments invariantly via
both neutral directions (`propagate.rs:272–281, 412–452`). Different paths
emit `NominalCastNeeded` (`:282–291`), so they must not be represented as a
generic constructor mismatch without accounting for the cast/diagnostic path.
The `wrap` declaration constructs an invariant owner argument in
`lowering/body/type_decl.rs:368–417`; focused fixtures include
`constraints/tests/case_01.rs:1227–1259` and
`lowering/tests/case_04.rs:649–665`.

The forced local effect-binder path selects an effect variable from compact
Function slots, marks it non-generic, then explicitly adds it to the scheme
quantifiers when it reaches the environment. An annotated parent routes local
reads through saved-scheme instantiation; without that annotation they remain
live (`lowering/expr/tail.rs:970–1011, 1241–1419`). Ordinary use instantiation
maps each listed TypeVar once and clones value, recursive, and Function-effect
occurrences through that same map. Thus the joint-use renaming theorem must
preserve one identity across occurrence roles, rather than freshening a
TypeVar separately by a value/effect label.

These locations characterize the Oracle implementation but do not supply the
replacement's algebra, public type normalization, or proof of principality.
The exact latent-effect denotation, weighted row transport, specialization
failure relation, and ordered diagnostics remain to be specified and proved.

## Current Yulang3 implementation boundary

The current live polarized algebra is in `crates/yu-solver/src/term.rs`:
branded terms, variable kind/polarity/ordinal views, and four-slot Function
views for argument, argument effect, result effect, and result. The live
`InferenceSession` owns direct `VariableBounds` and `EffectBounds`, separate
levels/metadata, and mutable constraints. Fresh-value/effect and constraint
entrypoints are `fresh_value_at_level`, `fresh_effect_at_level`,
`constrain_live_value`, and `constrain_live_effect` in `crates/yu-solver`.
These are representation candidates only; reuse depends on the approved
successor semantics.

The closed representation in `crates/yu-types/src/lib.rs` stores a positive
predicate, quantifier count, recursive-bound span, and arena brand. Current
F5c normalization/finalization and `F5cGeneralizer` are the closed-scheme
production path. Component execution builds and finalizes one draft per
member, installs the closed schemes, and then routes incoming uses through
those schemes; internal uses remain a separate live-root path. A replacement
therefore has to replace component publication, incoming routing, and retained
module results together. Polarity and four Function slots may be reusable
concepts; the current F5 Q/R closed-scheme pipeline is not an independent
intrusion implementation.

There is no implemented Rust `scheme_for` formatter/API in the current
checkout. `SolvedProjection` is coarse (`Int`/`Unknown`/`Never` for values and
`Empty`/`Unknown` for effects), while solver errors expose occurrence/cause
and a small shape classification. The eventual public scheme observation
contract therefore still needs a deliberate design; this map does not infer
or select one.

Sources: Oracle `propagate.rs`, `row_effect.rs`, `bounds.rs`,
`specialize2/type_graph.rs`, `specialize2/effect.rs`, and the cited lowering
fixtures; Yulang3 `crates/yu-solver/src/term.rs`, `lib.rs`, and
`crates/yu-types/src/lib.rs`. No code, tests, Python, or measurements were
used or changed.
