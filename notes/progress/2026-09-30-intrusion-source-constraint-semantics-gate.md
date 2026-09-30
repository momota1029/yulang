# Intrusion source-constraint semantics gate

Date: 2026-09-30
Status: candidate proof direction; unreviewed; no implementation authority
Scope: separate the successor's declarative source meaning from Oracle projection
Governing decision: user priority recorded in the redesign charter and q-bound successor draft

## Direction

The successor is required to retain meaningful source constraints, preserve
soundness/principality, and accept final well-typed programs. It is not
required to reproduce the Oracle's inference-stage scheme projection. Therefore
an exact simulation of the Oracle's `CompactRoot` selection and polarity
erasure is not the semantic foundation for the successor. It remains useful
for explaining Oracle observations and comparing final acceptance, but the
successor should derive its generalized component from a declarative
source-constraint relation and keep the constraints that relation requires.

This adjusts the next proof gate. The previous plan to prove that Oracle's
ordered root projection selects the exact graph retained by intrusion risks
making the Oracle's q erasure an implicit authority again. The needed direction
is instead:

```text
source syntax
  -> declarative source constraints and binder ownership
  -> generalized component retaining the required obligations
  -> per-use parent transport
  -> principal root/use relation
  -> final acceptance comparison with the frozen Oracle
```

The parent-transport fiber lemma proves only the third-to-fourth step, given
an exact graph and partition. It does not establish source-constraint
generation, typing adequacy, or SCC ownership.

## Candidate declarative interface

For a program `P` and a fixed outer environment `η`, define a declarative
judgment that generates a finite regular constraint graph and its identity
ownership:

```text
Γ; η ⊢ P ⇓ (C_P, A_P, L_P, roots_P, uses_P)
```

Here `C_P` contains every subtype, effect, row, role, and runtime-boundary
obligation required by the language semantics; `A_P` are identities shared
with the outer environment; `L_P` are identities owned by the binding/SCC;
`roots_P` maps definitions to exposed values; and `uses_P` records incoming
contexts. A candidate source well-typedness judgment is existence of a joint
assignment satisfying the declaratively generated constraints and every
required use context:

```text
WellTyped(P, η)  iff  ∃ν. Sat(C_P, η, ν) ∧ UsesOK(roots_P, uses_P, η, ν)
```

The same source-local identities used inside an SCC remain shared in `C_P`.
Each external polymorphic use substitutes fresh identities for the binding's
owned ports, while all anchors in `A_P` resolve through the same `η`. A root's
principal relation is the projection of this joint satisfying relation onto
its exported root and use observations, followed by the language's declared
subsumption rule. This uses the finite regular constraint graph directly and
does not require a pointwise least assignment.

This is only a signature for the missing semantics. It is not yet a definition
of Yulang well-typedness: the judgments for source forms, effects and handlers,
SCC member ownership, diagnostics, and runtime checks must be specified and
proved independently of either compiler's implementation.

## Relation to Oracle compatibility

For every `P` in the eventual supported envelope, compare the final Oracle
result with the independently defined `WellTyped(P)`. If they agree, final
acceptance parity is required. If they disagree, produce a concrete source
counterexample and record whether the Oracle accepts an ill-typed program or
rejects a well-typed one; apply the approved priority of soundness and
principality over Oracle compatibility. Inference-stage scheme text and phase
differences remain outside this comparison.

This does not excuse broad unmeasured divergence. It replaces a scheme-format
comparison with a final accepted-program comparison grounded in an independent
typing judgment. The envelope must still be declared, and all observed
differences inside it must be classified.

## Immediate proof sequence

1. Write declarative generation rules for the existing pure term fragment:
   variables, integer literals, lambdas, application, recursive definition
   groups, and incoming uses.
2. Prove source constraint generation and the generalized-component graph
   satisfy the same assignment relation, including the `pub f x = x f`
   application bound that the Oracle later erases during projection.
3. Apply parent transport to prove independent-use root relations with shared
   anchors; prove a root-principality statement by exact solution projection,
   not by pointwise least assignment.
4. Add latent effects, tuple/record/nominal rules, and the remaining supported
   source forms as separate conservative extensions; then compare complete
   final acceptance with the frozen Oracle.

The first three steps are a foundation, not a reduced completion target. The
full charter still requires effect hygiene, ordered SCC lifecycle, failure and
publication behavior, and sufficient implementation and verification.
