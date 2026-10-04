# Direct attacks on callback and structural main gates

Date: 2026-10-04
Status: theorem-gate finding; no semantic decision or implementation authority

This record reports direct attempts at the two current main gates. The callback
lane has one exact missing theorem premise. The structural lane has one exact
regular-completion boundary. Neither result authorizes a new carrier, semantic
rule, or support-envelope change.

## Pure-value callback / Function adequacy

**Result: the main theorem remains open at the source-to-endpoint adequacy
theorem; its bound clause has one decisive missing endpoint-bound
factorization premise, even with State excluded.**

Keep the approved B callback generation, actual Pure introduction and §21
entry, callback-slot typed invocation view, distinct receipts, and settled
`d⁻`, `d⁺`, and `b⁺` locations. The direct attempt granted equal challenge
domains and execution correspondence over the largest assembled immutable
source fragment. It still could not derive the required full-bound inclusion.

The relevant statements have different directions and scopes:

```text
source adequacy:      Sem_actual(d) ⊆ P_actual(d)
execution transport:  Sem_actual(d) corresponds to checked execution
required conclusion:  P_actual(d) ⊆ P_checked(d)
```

The source reference remains the exact collecting relation `Sem` defined by
the source-interface adequacy draft. `P_actual` and `P_checked` are endpoint
presentations whose denotations may conservatively cover `Sem`; exactness is
not a separate language-semantic choice here. The unresolved obligation is to
factor the denotation of the actual endpoint presentation, including its
permitted slack, through the linked checked view.

The minimal logical countermodel to the execution-only inference has one
challenge, an execution returning `0`, an actual bound admitting `{0,1}`, and
a checked bound admitting only `{0}`. Both bounds contain the execution, but
the required containment fails. This refutes that proof step; it is not a
Yulang source-program counterexample and does not refute the selected lift.

For the full query, the theorem must construct checked-challenge admission
independently of comparison success and establish both `D_checked ⊆ D_actual`
and the observation-bound inclusion. Even granting equal domains and
execution correspondence on the State-free fragment, the latter still does
not follow. Its single missing premise is:

> Every observation admitted by the actual synthesized endpoint's complete
> bound factors through its existing `J_arg`, `J_body`, designated result
> consumer, and `J_call` composition under the same `ν,K,D` fiber, and that
> factorization is admitted by the linked checked view.

This is a full-bound factorization obligation, not an exactness requirement.
Event routing, `Flow`/`Observe`, and finite history correspondence account for
actual observations; they do not account for additional observations allowed
by an endpoint bound. Excluding State removes store-realization obligations
but does not remove this gap: it already occurs for the stateless terminating
Pure identity. No new user semantic choice or representation deficiency has
been demonstrated.

Governing sources: [callback context delivery](../design/2026-10-03-callback-context-delivery.md)
§§2–5, 7–8; [typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md)
§9; [source interface adequacy](../design/2026-10-02-source-interface-adequacy-theorem.md)
§§2–4. The previous theorem-level attempt and evidence remain in
[value-entry bind/projection](2026-10-04-value-entry-bind-projection.md).

## Structural regularity / finite presentation

**Result: finite residual presentation remains available, but regular-witness
decidability for the full shifted-descriptor/variance fragment is open at one
regular-completion theorem.** No undecidability reduction or source counterexample
was found.

After the existing rational equality quotient and finite-alphabet/atom
normalization, describe each quotient root `q` by address languages
`D_q ⊆ I*` for present paths and `H_q^h ⊆ D_q` for heads `h`. Record heads
carry their exact finite label masks. Each original bound `b` has activation
languages `A_b⁺, A_b⁻`; these retain its identity and orientation rather than
composing successful comparisons. Finite `I` contains tagged Record fields
and ranked-constructor coordinates.

The exact constraints include:

- descriptor equations transport domain and head facts by prefix shift,
  `D_q(iw) ↔ D_c(w)` and `H_q^h(iw) ↔ H_c^h(w)`;
- each active original bound checks local heads and Record width at its current
  address, then descends only through fields required by the current upper
  endpoint;
- descent preserves, reverses, or duplicates orientation according to the
  declared variance, with both directions for invariant coordinates;
- finite permissions and rigid-name identities remain attached to their
  original roots; guards and joint `Phi/K,D` predicates remain separate
  constraints.

A regular assignment induces regular domain/head/activation languages. In the
other direction, regular languages satisfying these coherence, descriptor,
and activation constraints give a finite regular graph assignment and a
post-fixed structural simulation for each original bound. Thus the precise
remaining question is whether this simultaneous finite system has a
terminating regular-completion/decision procedure (or a regular-model theorem
paired with a terminating satisfiability procedure). This statement does not
prove decidability or undecidability.

The tempting direct MSO proof over the ordinary full address tree is invalid.
The descriptor relation `v = 0u` is not an MSO-definable relation there: if it
were, restricting marks to `u=10ⁿ` and `v=010ᵐ` would define equality of the
two unbounded suffix lengths across distinct root branches, which no finite
parity tree automaton can enforce. Reversing addresses makes prefix shifts
local but turns ordinary child descent into a nonlocal prefix operation. This
rejects that MSO route only; it is not an undecidability result.

The standard recursive structural subtype theorem does not directly transfer:
its structural relation requires matching tree domains, while its
nonstructural relaxation uses global least/greatest types. Mandatory Record
width instead requires selective per-field omission while live fields remain
proper types. A proposed fixed-arity encoding with global `Top` admits spurious
solutions unless it separately proves recursive source-image preservation.
See [Niehren, Priesnitz, and Su, *Complexity of Subtype Satisfiability over
Posets*, §§2, 4.1, 5](https://www.cs.ucdavis.edu/~su/publications/esop05.pdf).

A direct transfer of the known guarded-BPA undecidability reduction also fails
at a precise premise. DeYoung et al. encode a BPA process by transparent,
parameterized recursive constructor families `t_X[α]`, whose recursive calls
transform the continuation argument; their reduction is stated in §2.3.2 and
Theorem 2.1 of [*Parametric Subtyping for Structural Parametric
Polymorphism*](https://ankushdas.github.io/docs/popl24.pdf). Yulang's scoped
regular fragment instead assigns finite regular graphs to finitely many free
classes; a recursive scheme bound is a binder reference with one lower/upper
pair, not a type-level operator that is re-applied to a changed argument.
The inspected type-declaration authority defers alias/nominal semantics and
does not authorize transparent parameter-changing recursion.

This difference is substantive: for the guarded equations `X = a·X·Y + b·ε`
and `Y = c·ε`, the paper's construction gives
`t_X[α] = {a: t_X[t_Y[α]], b: α}` and
`t_Y[α] = {c: α}`. In `t_X[{}]`, the subtree after `a^n` has a `b` child
consisting of exactly an `n`-long `c` chain. These subtrees are pairwise
non-bisimilar, so this constructed unfolding has no finite regular graph
presentation. This validates the missing-premise distinction; it is not a
Yulang counterexample and does not exclude a separate reduction directly into
finite regular constraints.

Finite constrained residual presentation, regular-witness existence, and
principal/effective projection of the full solution fiber remain distinct
claims. The first is covered by existing scoped residual work; neither a
single witness nor that presentation proves the latter two. Existing bounded
Record saturation remains within its stated scope. No queue-machine candidate
is advanced here. The current structural gate is therefore still the
simultaneous regular-completion theorem, not an undecidability result. For the
literature reduction specifically, the exact absent premise is transparent
parameter-changing recursive type constructors; admitting that premise would
expand language authority rather than follow from regular graph recursion.

## Work boundary

These are theorem findings, not completed gates. Callback closure depends on
the one full-bound factorization premise above. Structural closure depends on
the one regular-completion theorem above. No tests, builds, Oracle runs,
measurements, compiler edits, or design-status changes were made.
