# Relational abstraction congruence criterion

Date: 2026-10-02
Status: reviewed candidate lemma; non-authoritative
Scope: one shared adequacy test for finite presentations of source relations
Implementation authority: none

## Criterion

Let `T ⊆ X × Y` be a source relation, with input and output presentations
`α_in : X → A` and `α_out : Y → B`. An exact abstract transformer
`t : A → P(B)` satisfying

```text
t(α_in(x)) = { α_out(y) | (x,y) ∈ T }
```

exists on the image of `α_in` iff equality of input presentations implies
equality of the abstract output sets. Necessity follows by applying `t` to
equal abstract inputs. For sufficiency, define `t` by choosing any concrete
representative of each presented input; the congruence premise makes the
choice irrelevant. Empty output sets are included, so output existence is
preserved. Divergence or stuckness must be included in `Y` if it is an
observable distinction.

This is a criterion on abstraction, not a source rule. It applies to local
bind/boundary/handler relations. Generalization and intrusion must use the
whole assignment-indexed relation as `X` and `Y`, including rigid imports,
owned identities, roots, and the relevant projection or parent transport; a
proof at a single assignment does not establish lifecycle preservation.

## Shallow-handler discriminator

At one fixed `(ρ,ν,κ)`, take two computations with the same visible `F`
request, payload, family instance, and typed may-row `{F}`:

```text
c₀ = Request(F, (), λ_. Return(v))
c₁ = Request(F, (), λ_. Request(F, (), λ_. Return(v)))
```

A visible `F` arm resumes the raw continuation once and returns its result.
The shallow handler consumes the first request. Its raw continuation resumes
outside that activation, so output supports are `∅` for `c₀` and `{F}` for
`c₁`. A support-only input presentation identifies them and therefore cannot
produce an exact pointwise handler map. This is an information-loss result
for the row quotient, not a reason to add a callback, demand, route, or
source-site-specific selector.

The collecting support over the two examples is `{F}`, so the counterexample
does not require exact continuation-sensitive inference. A coarser solver may
use a sound collecting result when it has a least representable output in its
declared ordering and later composition remains sound and principal. Finite
syntax alone does not guarantee that least result. The output presentation
must retain symbolic typed-family predicates and their incidence `K,D` at
the same assignment; materialized support union is insufficient.

## Architecture and review

An architect audit compared typed may-rows, a complete-interface relation,
and continuation-bearing computations. The proposed division is one
source-indexed relation over complete typed interfaces, generated from
continuation-bearing source computation and typing; exact resumable behavior
is a semantic reference, not the inference representation. The finite
interface must prove the congruence or use a least sound widening, retaining
typed-family fibers.

- Pre-write `compiler_referee` review accepted the criterion subject to
  clarifying that it characterizes pointwise exact quotienting, not the
  already-defined collecting transfer; it also required a same-input-fiber
  witness and an explicit least-output premise.
- Pre-write `spec_auditor` review required the theorem to keep inference
  conservative and symbolic `K,D` constraints, and not enlarge authority.
- The first post-write review found that single-valuation reasoning must not
  be used to certify whole-relation generalization or intrusion. The criterion
  was generalized to `T ⊆ X × Y`, with whole-relation inputs/outputs for those
  lifecycle maps. Empty output sets were narrowed to output existence.
- A fresh compiler-referee delta review closed that repair with no remaining
  findings. The spec audit found and closed a minor scope phrase that could
  imply the whole abstract fiber contained only the two counterexample
  computations.

This lemma does not prove source typing adequacy, finite presentation
closure, solver principality, or the symbolic lifecycle. It is a common test
for those later proofs. The coupled-interface design remains a draft; no
compiler code or tests changed. `git diff --check` passed.
