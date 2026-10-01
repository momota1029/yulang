# Nested let-polymorphism with retained graph schemes

Date: 2026-09-30
Status: candidate declarative extension and conditional adequacy proof; reviewed within the stated pure fragment; not implementation authority
Scope: pure `Var`/`Int`/`Lambda`/`Apply` plus non-recursive `let`; no effects or recursive groups inside the let RHS
Governing records: `2026-09-30-intrusion-pure-source-typing-rules.md`, `2026-09-30-intrusion-pure-recursive-group-adequacy.md`, `2026-09-30-intrusion-parent-transport-fiber-lemma.md`

## Graph scheme

A graph scheme is a finite regular constraint graph with a root and an explicit
ownership split:

```text
S = (C, root, Q, A)
Q ∩ A = ∅
```

`Q` is the set of scheme-local identities. `A` is the set of fixed outer
anchor identities referenced by the graph. For a fixed `η : A → D`, define

```text
Inst_S(η) = {
  T | ∃ν : Q→D. Sat(C,η,ν) ∧ eval(root,η,ν) ≤ T
}
```

This relation, rather than a rendered type tree, is the scheme meaning. Local
identities that affect the root only through bounds remain quantified even if
they do not occur syntactically in `root`. No polarity-only erasure is part of
this rule.

Instantiation chooses a fresh set `Q_u` disjoint from all current identities
and a bijection `ρ_u : Q→Q_u`, fixes every anchor in `A`, and returns the
renamed graph `ρ_u(C)` and root `ρ_u(root)`. The parent-transport fiber lemma
shows this preserves `Inst_S(η)` exactly. Distinct uses choose pairwise
disjoint fresh ranges and may share only the fixed anchors.

## Declarative let rule

Extend a semantic environment `Γ` so each source name maps either to one
monomorphic value (`Mono(T)`) or to a polymorphic type set (`Poly(P)`, where
`P⊆D` is upward closed under `≤`). A monomorphic variable occurrence has
exactly its mapped type; a polymorphic occurrence may choose any `T∈P`. Each
occurrence makes its choice independently. A graph scheme `S` represents the
semantic entry `Poly(Inst_S(η|A_S))`; it is not itself the declarative entry. All expression
rules from the pure source-typing note remain unchanged, with the variable
rule interpreted through this environment.

For fixed outer anchor assignment `η`, write
`Types_(Γ,η)(e) = { T | Γ,η ⊢ e : T }`. A graph scheme `S₁` is an exact
principal representation for `e₁` under `Γ,η` when
`Inst_S₁(η|A₁) = Types_(Γ,η)(e₁)`, where `η|A₁` is restricted to the
scheme's free anchors. The declarative judgment is indexed by `η` throughout.
Its `Let` rule uses the independently defined source type set:

```text
P₁ = Types_(Γ,η)(e₁) ≠ ∅
Γ[x↦Poly(P₁)],η ⊢ e₂ : T
──────────────────────────────────────────── Let
Γ,η ⊢ let x=e₁ in e₂ : T
```

The rule depends only on source typing, not on a graph scheme or generator.
Its nonempty condition requires a valid RHS binding even if `x` is unused.
Every occurrence of `x` may choose a different type from `P₁`. This gives
let-polymorphism directly in the declarative relation; it does not reuse
Yulang's inference-stage scheme format or acceptance phase.

## Generation and generalization boundary

Let `Anch(Ξ)` be the union of (a) identities in monomorphic endpoint entries
of the generation environment and (b) anchors exposed by polymorphic scheme
entries. Every scheme lookup clones all of its `Q` identities freshly and
retains its `A` anchors. Precisely, if `Ξ(x)=Poly(C,r,Q,A)`, a lookup
allocates a fresh bijection `ρ:Q→Q'`, returns root `ρ(r)`, and contributes
`ρ(C)` with anchors fixed. A monomorphic lookup returns its endpoint and no
new obligations. Lambda parameters and application results also use fresh
identities; the other syntax cases use the pure source-generation rules. For
an RHS generation result `(t₁,C₁)`, define:

```text
Q₁ = Identities(C₁,t₁) \ Anch(Ξ)
A₁ = Anch(Ξ) ∩ Identities(C₁,t₁)
S₁ = (C₁,t₁,Q₁,A₁)
```

Identities in `Anch(Ξ)` that do not occur in the RHS are omitted from `A₁`.
Freshness requires `Q₁` to be disjoint from every identity in the receiving
context. Thus a lambda parameter or a shared outer inference variable cannot
be generalized by an inner let, while every RHS-local graph identity is
quantified. Nested scheme instantiation identities created while generating
the RHS are RHS-local and therefore enter `Q₁`; anchors inherited from those
schemes remain in `A₁`.

The generator for `let x=e₁ in e₂` works as follows:

1. Generate `(t₁,C₁)` for `e₁` under `Ξ`, using fresh local identities for
   each polymorphic lookup.
2. Form `S₁` using the partition above.
3. Generate `(t₂,C₂)` for `e₂` under `Ξ[x↦Poly(S₁)]`. Each occurrence of `x`
   inserts a separately renamed copy of `C₁` and uses its renamed root.
4. Return `(t₂, C₁ ∪ C₂)`.

Retaining the original `C₁` checks that the binding itself has a typing,
including when `x` is unused. Its scheme lookups use disjoint fresh copies,
so each use can choose a different local assignment. Repeated uses share the
fixed `A₁` anchors but do not share `Q₁` assignments.

## Conditional adequacy theorem

Relate generator and semantic environments by `Ξ ≈_η Γ`:

- `Ξ(x)=Mono(u)` iff `Γ(x)=Mono(eval(u,η))`;
- `Ξ(x)=Poly(S)` and `Γ(x)=Poly(P)` iff `Inst_S(η|A_S)=P`.

The source-name domains must agree. `η` assigns every identity in
`Anch(Ξ)` and every anchor exposed by the corresponding semantic environment.
All identities generated by an expression are fresh from those anchors. This
rules out assigning different semantic types to the same
monomorphic endpoint and makes outer identity sharing explicit. Poly entries
are related by denotation, not by syntax or binder IDs.

**Environment extensionality.** If two semantic environments have the same
monomorphic values and equal polymorphic sets `P` for each name at the fixed
anchor assignment, then they assign the same type set to every expression.
Induct on the expression: variable lookup uses the equal sets; integer,
lambda, application, and subsumption preserve equality; a `Let` RHS has the
same `Types` set by induction, so the resulting `Poly(P₁)` extension is also
equal in both environments. This lets a graph scheme representation replace
a direct semantic type set once `Inst_S=P` has been proved.

Assume the monomorphic expression-generation correspondence from
`2026-09-30-intrusion-pure-source-typing-rules.md`. A structural induction on
the full extended syntax (`Var`, `Int`, `Lam`, `App`, `Let`) proves, for every
`Ξ ≈_η Γ`, that if generation returns `(t,C)`, with
`Q=Identities(C,t)\Anch(Ξ)` and
`A=Anch(Ξ)∩Identities(C,t)`, then:

```text
Sat(C,η|A,ν) => Γ,η ⊢ e : eval(t,η,ν)
Γ,η ⊢ e : T => ∃ν. Sat(C,η|A,ν) ∧ eval(t,η,ν) ≤ T
```

Consequently `S_e=(C,t,Q,A)` satisfies the exact equation
`Inst_{S_e}(η|A)=Types_(Γ,η)(e)`. This is the strengthened invariant needed
for generalization; it is not assumed from scheme validity.

The base cases are as follows. A monomorphic variable uses `Ξ≈_ηΓ` and
subsumption; a polymorphic variable clones its scheme and uses the
parent-transport fiber bijection to preserve the scheme denotation; an
integer uses its fixed root. Lambda extends both environments with the same
fresh parameter value, applies the body induction hypothesis, then puts that
parameter identity in the enclosing expression's local set. Application
combines the two disjoint local assignments and uses the Function subtyping
law to match the generated application obligation.

For `Let`, apply the induction hypothesis to `e₁` first. It proves
`Inst_{S₁}(η|A₁)=Types_(Γ,η)(e₁)`, so the generator's `Poly(S₁)` entry
represents the declarative `Poly(P₁)` entry. The nonempty condition is
equivalent to existence of a satisfying base assignment for `C₁`. Apply the
induction hypothesis to `e₂` under these extensionally equal environments.
In the forward direction, a satisfying
assignment for `C₁∪C₂` contains both the base witness for `C₁` and one witness
for each fresh scheme-use copy in `C₂`. In the reverse direction, the
declarative let derivation supplies a base RHS witness and each occurrence
chooses a type in `Inst_{S₁}`; the definition of `Inst` supplies a witness for
that occurrence's copy. All local ranges are disjoint and every shared anchor
uses the same `η`, so these witnesses combine into one assignment for
`C₁∪C₂`.

Thus the generated scheme's denotation equals the independently defined
declarative type relation for every fixed anchor assignment. Root principality
follows from this equality and ordinary upward subsumption, not from defining
`Inst` alone. No least simultaneous value for all graph identities is
required.

### Composition after a recursive SCC

The nested-let theorem composes with the recursive-group theorem without
introducing a second instantiation rule. Suppose a completed pure SCC exposes
each member `d` through a graph scheme `H_d`, and for the fixed outer
assignment its denotation equals the declarative member set `P_d`:

```text
Inst_{H_d}(η|A_d) = P_d
```

Relate the endpoint environment entry `Ξ(d)=Poly(H_d)` to the semantic entry
`Γ(d)=Poly(P_d)` by the already-defined environment relation `Ξ ≈_η Γ`.
The extended-expression adequacy theorem then applies to any ordinary
non-recursive `let x=e₁ in e₂` generated under that environment. Each use of
`d` in `e₁` or `e₂` freshens the member scheme's complete local graph, fixes
the same outer anchors, and contributes its renamed constraints to the
enclosing graph. The Let induction case therefore combines the SCC root
fiber with independently fresh use fibers by the same disjoint-assignment
argument; it does not reopen or freshen the SCC's internal recursive uses.

This is a compositional corollary conditional on the SCC scheme denotation
equation and the common anchor assignment. It covers ordinary lets after a
pure SCC, but not a recursive group nested inside a let RHS, effectful
bindings/value restrictions, distinct per-member fetch boundaries, or the
Oracle scheduler's versioned root projections. It establishes no new
source-to-Oracle adequacy premise.

## Ownership witnesses

For `let id = λx.x in id 1`, RHS generation yields
`root=Fun(a,a)`, `C=∅`, `Q={a}`, and `A=∅`. The lookup in `id 1` gets a fresh
`a'`; its application obligation is
`Fun(a',a') ≤ Fun(Int,b)`. Choosing `a'=Int` and `b=Int` satisfies it. A
second occurrence of `id` gets a distinct identity, so it can choose a
different argument type without changing the first use.

For `λy. let k=λx.y in k 1`, the inner RHS root is `Fun(a,y)` with
`Q={a}` and `A={y}`. Each lookup freshens `a` and fixes `y`. Thus the inner
let cannot capture the enclosing lambda parameter, even though the scheme
retains all RHS-local identities. The argument `a` is kept explicitly in the
root relation; removing it to a polarity extreme would be an optional
optimization requiring a separate preservation proof.

## Boundary and composition consequences

For a pure non-recursive let, the partition is derived rather than guessed:
`Q₁` contains all fresh RHS identities and `A₁` contains precisely the RHS
identities already owned by the environment. In particular:

- an inner let cannot capture a lambda parameter or a shared outer variable;
- an outer polymorphic scheme's local identities are freshly copied into the
  RHS and may be generalized by the inner let, while its anchors remain fixed;
- two uses of one local scheme share outer anchors but receive disjoint local
  assignments;
- unused bindings still have to admit a satisfying RHS assignment;
- nested lets compose by carrying each binding's base constraints in the
  enclosing graph and cloning its scheme constraints for every use.

This also gives the recursive-group subcase a clean composition point: once
the recursive SCC has produced member graph schemes, they enter `Ξ` as
`Poly(S_d)`. An ordinary let RHS that uses a member receives fresh copies of
the complete member graph; its own local variables can then be generalized
without capturing the SCC scheme's fixed anchors.

## Limits

This is a candidate proof for a custom pure declarative system, not yet proof
that the rule matches Yulang's full source semantics. It excludes effects,
handler hygiene, roles, value/computation fetch distinctions, recursive
groups nested in expressions, diagnostics, failure scheduling, and runtime
entrypoint checks. It assumes graph schemes carry all constraints needed to
characterize their root relation. The final accepted-program comparison with
the frozen Oracle and the implementation design remain open.

## Review record

On 2026-09-30, this M3 semantic-contract slice received a compiler-referee
review and a spec-auditor review. They found and closed environment-coherence,
extended-induction, anchor-notation, and scope-wording gaps. The final delta
review found no remaining concrete issue within this artifact's stated
pure-fragment scope. These reviews did not assess the
full Yulang type/effect semantics, an implementation, runtime soundness, or
Oracle final-acceptance equivalence. This note remains a candidate proof and
does not authorize implementation.

## Follow-up: pure monomorphic binding (value-restriction subcase)

The earlier `Let` rule generalizes every RHS and therefore excluded Yulang's
value restriction. The source distinction should be phrased from the
value/computation boundary, not as an Oracle `BindingFetch` semantic tag. For
the pure fragment, let `Value(e)` be the source-derived predicate that RHS
evaluation yields a value without executing a computation. Define one binding
judgment with two cases:

```text
Value(e₁)   P₁ = Types_(Γ,η)(e₁) ≠ ∅   Γ[x↦Poly(P₁)],η ⊢ e₂ : T
──────────────────────────────────────────────────────── BindValue
Γ,η ⊢ let x=e₁ in e₂ : T
```

```text
¬Value(e₁)   Γ,η ⊢ e₁ : T₁   Γ[x↦Mono(T₁)],η ⊢ e₂ : T
──────────────────────────────────────────────────────── BindComputation
Γ,η ⊢ let x=e₁ in e₂ : T
```

The computation case chooses one RHS type `T₁` for the binding and shares it
across every lookup of `x`. It still permits ordinary subsumption at each
lookup. It does not prohibit a later enclosing value boundary from quantifying
identities local to this entire subexpression; those identities become ports
of the enclosing scheme and are freshened only when that enclosing value is
instantiated.

The corresponding graph generation case is direct composition:

```text
Ξ ⊢ e₁ ⇓ (t₁,C₁)     Ξ[x↦Mono(t₁)] ⊢ e₂ ⇓ (t₂,C₂)
──────────────────────────────────────────────────── GenerateBindComputation
Ξ ⊢ let x=e₁ in e₂ ⇓ (t₂,C₁∪C₂)
```

There is no fresh clone of `C₁` at an `x` lookup: all lookups refer to `t₁`
under the same graph assignment. `C₁` remains even when `x` is unused, so the
binding itself must be typable. For an outer scheme, every fresh identity from
`C₁∪C₂` remains local to that scheme unless it is already an outer anchor.
The computation remains monomorphic within one enclosing scheme instance,
while separate instantiations of that outer scheme freshen its local graph
identities independently.

**Conditional adequacy.** Assume the monomorphic expression generation
correspondence and environment relation `Ξ≈_ηΓ` from the earlier theorem.
Forward, a satisfying assignment for `C₁∪C₂` gives
`T₁=eval(t₁,ν)`, types `e₁:T₁` by the first graph correspondence, and types
`e₂` under `x↦Mono(T₁)` by the second; together these are `BindComputation`.
Reverse, a source derivation supplies `T₁` and separate witnesses for `e₁`
and `e₂`. The RHS graph correspondence gives a root value
`T₀=eval(t₁,ν₁)≤T₁`. Replacing a `Mono(T₁)` environment entry by the more
precise `Mono(T₀)` preserves the body derivation: every occurrence typed at
`T₁` can be reconstructed from `T₀` using subsumption. Apply the expression
generation theorem to `e₂` with that shared root assignment. Freshness of
body-local identities lets the two witnesses combine into one assignment for
`C₁∪C₂`. As in the generalized-let theorem, this is exact equality of the
resulting scheme denotation with the declarative type set, modulo its outer
anchors.

This closes only the pure, non-recursive local computation-binding case. It
does not define the effectful computation interface: that case must sequence
the complete resumable relation and preserve symbolic typed-family formulas
monomorphically, including through any enclosing generalization/intrusion.
Top-level computed roots additionally append to the source-order execution
observation; a source-level module theorem must combine that observation with
the same monomorphic binding rule. The value/computation predicate itself is
not a solver selector; it is derived from source evaluation and controls
whether the binding's identities are shared or independently chosen.
