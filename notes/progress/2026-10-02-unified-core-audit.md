# Unified effect/intrusion core audit

Date: 2026-10-02
Branch: `research/simple-sub-intrusion`
Status: independent architecture/soundness audit; non-authoritative
Implementation authority: none

## Question

Does the current coupled-interface candidate meet the user's preference for a
small theory, or does it merely rename source-site-specific rules under one
large relation?

## Audit result

An independent architect and compiler-referee audit found no new contradiction
in the corrected conditional transport lemmas. Both recommend retaining the
assignment-indexed complete-interface relation as the current mathematical
candidate, while treating it as a factorization proposal rather than a defined
or certified source semantics.

For fixed imports `ρ`, the candidate is:

```text
Rel_C(ρ) ⊆ { (ν, I) }
```

`ν` is one assignment to source-owned binders; `I` is the complete observable
value/computation interface. Four constructions suffice for the current
presentation: fiber product over the same assignment, relational composition,
predicate restriction, and consistent identity transport. Projection is a
direct image of this relation. This is the smallest candidate found so far;
adding a selector or obligation calculus for each Oracle case closes none of
the outstanding proof gaps.

## Cases as consequences, not semantic rules

| Requested operation | Derivation from the common relation | Additional proof needed |
|---|---|---|
| Row split/union | Project or combine support coordinates while retaining the shared assignment and predicates | Factorization before independently solving split pieces |
| Filtering | Map only the request-support coordinate and preserve the satisfying assignment domain | Formula/incidence transport for every dependent view |
| Handler subtraction | Compose the full continuation-bearing interface with the source handler image; project output support afterward | Source visibility/transition adequacy and complete output lifting |
| Callback boundary | Compose caller, callee and callback interfaces under one assignment and ordered machine context | Source rules for adaptation, forcing, nested contracts and escapes |
| Generalization | Existentially bind owned coordinates relative to fixed imports while retaining the full interface relation | Correct source view/binder selection and fixed-import solution correspondence |
| Instantiation | Consistently rename the complete owned namespace while fixing imports | Source-use independence and complete namespace transport |
| Intrusion | Reindex/pull back the relation along the parent assignment map | Injective equivariance; for non-injective maps, observation-preserving quotient theorem |

These operations share a carrier and algebra, not one preservation theorem.
Their proof obligations remain distinct because their maps have different
fibers and observations. This is a proof decomposition, not a justification
for separate semantic stores.

## Semantic distinctions and bookkeeping

The audits classify as semantic: value versus computation behavior; typed
operation arguments and payload/result compatibility; source-derived sharing
of binders; rigid imports versus independently owned uses; and handler-relative
visibility/re-entry in the dynamic configuration. These can change admissible
assignments or observations.

`Sel_s` witnesses, `Demand` labels, obligation keys, numeric occurrence/owner
IDs, `D` dependency records, route certificates, and explicit `P`/`Theta` maps
are presentation or proof bookkeeping. The predicate represented by `K` and
the actual source sharing presented by `D` are semantic; their syntax and
storage are not extra semantic coordinates. Typed-family invariance must
remain symbolic in the same assignment across every lifecycle step, including
when its original request support is filtered to empty.

## Candidate comparison

- **Ground rows alone** have low syntactic cost but lose typed-family fibers,
  result/request correlations and continuation distinctions. They cannot be
  the authority under the symbolic-invariance requirement.
- **Rows plus independent selector/route/obligation analyses** duplicate the
  same meaning across solving, callbacks, handlers and transport. They remain
  possible executable presentations only if a coupling theorem proves that
  their combined denotation is the common relation.
- **Finite constrained complete-interface relations** have one carrier and
  reuse composition and transport laws. They are the preferred research
  candidate, but finite effective principal closure is unproved.
- **Exact resumable computation relations** give the source-level reference
  for soundness. Exact trace inference is not required; a conservative
  abstraction is acceptable if it is sound and principal in its chosen domain.

The abstraction-congruence counterexample remains decisive: two computations
with the same `{F}` support can yield residual supports `∅` and `{F}` after a
shallow handler, depending on the raw continuation. It rejects exact support-
only subtraction; it does not justify a new callback selector or exact-trace
inference.

## Open certification blockers

1. Source rules for binder ownership, nested concrete callback contracts,
   escaped-value lineage, and `Visible(q,h,κ)` are not yet defined. The
   frozen checker/runtime mismatch cannot choose these rules.
2. Substitution of formulas is not solver completeness. A subtype solve step
   must preserve the relevant observable solution fiber or retain a residual
   relation that does.
3. A least closed reachability approximation is not yet a principal type
   interface. Choose a bounded presentation and prove source correspondence,
   least representable handler images, and fixed-import lifecycle transport.
4. Oracle weights still have no independent denotation. Either omit them from
   the mathematical core or derive each retained routing transformation from
   the source relation and prove preservation, including repeated pushes and
   shared pops.

These are named proof gates, not new defects in the locally reviewed transport
lemmas. The nested concrete receiver and escaped-value lifetime decisions
remain unresolved. No implementation or test work is authorized by this
record.

## Review boundary

The architect compared candidate formulations by economy, composition,
principality, and proof reuse. The compiler-referee checked countermodels and
the symbolic lifecycle. Both audits were read-only; no code or tests changed.
Relevant sources: the non-authoritative coupled-interface core draft, the
callback-scope and symbolic-family transport records, and the reviewed
redesign charter. The next useful gate remains a precisely bounded source
transition/interface fragment whose finite presentation preserves the whole
typed-family solution fiber.
