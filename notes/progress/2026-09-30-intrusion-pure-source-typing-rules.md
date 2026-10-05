# Pure source typing rules for the intrusion foundation

Date: 2026-09-30
Status: candidate declarative rules; unreviewed; not implementation authority
Scope: monomorphic expression fragment used to ground the source-constraint contract
Governing source: `notes/progress/2026-09-30-intrusion-source-constraint-semantics-gate.md`

## Semantic fragment

Fix a preorder carrier `D` with a distinguished integer value `Int_D` and a
Function constructor `Fun_D` satisfying the pure Function subtyping law:

```text
Fun_D(A,R) ≤ Fun_D(A',R')  iff  A' ≤ A and R ≤ R'
```

Ignore effects and polymorphic schemes in this first fragment. The semantic
typing environment `Γ` maps variables to values in `D`; a separate
constraint-generation environment `Ξ` maps names to endpoint terms. The
monomorphic expression syntax is:

```text
e ::= x | integer | λx.e | e e
```

The declarative typing judgment includes subsumption and uses this application
rule:

```text
Γ(x)=T
────────── Var
Γ ⊢ x : T

──────────── Int
Γ ⊢ n : Int_D

Γ[x↦A] ⊢ e : R
──────────────────────── Lam
Γ ⊢ λx.e : Fun_D(A,R)

Γ ⊢ f : T₁     Γ ⊢ a : T₂     T₁ ≤ Fun_D(T₂,R)
────────────────────────────────────────────── App
Γ ⊢ f a : R

Γ ⊢ e : T     T ≤ U
─────────────────── Sub
Γ ⊢ e : U
```

The generation environment `Ξ` is interpreted under a graph assignment `ν` by
`⟦Ξ⟧_ν(x) = eval(Ξ(x),ν)`. The type-assignment judgment returns a finite
regular endpoint graph:

```text
Ξ ⊢ e ⇓ (t, C)
```

Its rules mirror the source constructors but allocate fresh graph variables
for lambda parameters and application results:

```text
Ξ(x)=t
────────────── Name
Ξ ⊢ x ⇓ (t, ∅)

──────────────────────── Integer
Ξ ⊢ n ⇓ (Int_D, ∅)

Ξ[x↦α] ⊢ e ⇓ (r,C)
──────────────────────────────────── Lambda
Ξ ⊢ λx.e ⇓ (Fun_D(α,r), C)

Ξ ⊢ f ⇓ (t₁,C₁)     Ξ ⊢ a ⇓ (t₂,C₂)    β fresh
──────────────────────────────────────────────────────── Apply
Ξ ⊢ f a ⇓ (β, C₁ ∪ C₂ ∪ { t₁ ≤ Fun_D(t₂,β) })
```

All endpoint variables range over `D`; a constraint set is satisfied when
each endpoint inequality holds after assignment. Recursive endpoint
back-edges, if present, are interpreted by direct assignment lookup rather
than by unfolding a recursive type.

## Correspondence theorem for this fragment

Assume `D` satisfies the Function law above. For every endpoint environment
`Ξ` and expression `e`, let generation produce `(t,C)`. Fix an assignment `η`
for the free anchors of `Ξ`; generated lambda/application variables are fresh
from those anchors. An assignment `ν` must extend `η`, assign every generated
variable appearing in `t` or `C`, and satisfy `C`. The constraints have the
following correspondence with declarative typing:

```text
ν extends η, assigns all generated variables, and satisfies C
  =>  ⟦Ξ⟧_ν ⊢ e : eval(t,ν)

⟦Ξ⟧_η ⊢ e : T
  =>  there is an extension ν of η satisfying C with eval(t,ν) ≤ T
```

The proof is induction on expression generation and typing. Name and integer
cases are immediate. For a lambda, extend the assignment with the chosen
parameter value and apply the body induction hypothesis; Function covariance
transports a body result that is below its declarative result type. For
application, the generated inequality supplies exactly the `App` premise for
the generated callee, argument, and result values. In the reverse direction,
the declarative `App` witness assigns the fresh result variable; if premise
types were widened by `Sub`, transitivity and Function variance recover the
generated application inequality from the original argument/result bounds.
`Sub` is represented by the `≤` allowance on the returned endpoint. The
Function law justifies both transports.

This establishes a small independent typing/constraint-generation interface;
it is not a Yulang compiler theorem yet. The candidate powerset carrier can
interpret the type constructors, but this note does not show that it is the
language's intended runtime type domain. The proof excludes recursive
definition groups, SCC ownership, let-polymorphism, external instantiation,
effects, rows, roles, diagnostics, and runtime entrypoint checks. Consequently
it establishes neither whole-program well-typedness nor Oracle-capability
equivalence.

The preorder premise is essential to the stated completeness theorem. Its
`Sub` rule and generation proof cannot be read as allowing arbitrary successful
concrete `A <: B` resolutions to chain: optional-record compatibility admits
`{foo?: string} <: {}` and `{}` `<:` `{foo?: int}` while rejecting the direct
comparison. With such anchors, the source term `x` can be widened twice but
Name generation retains only its original anchor. The exact counterexample
and the source-bridge obligation are recorded in the
[concrete-transitivity obstruction](2026-10-05-source-adequacy-concrete-transitivity-obstruction.md).

## Next extension

Add recursive definition groups with a monomorphic self placeholder per member
and a distinct exposed root where required by the source rule. State which
identities become per-use ports and which remain shared anchors. Prove the
joint assignment relation before adding projection or simplification. The
parent-transport fiber lemma applies after this ownership partition and
complete graph are fixed.
