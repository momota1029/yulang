# Pure recursive groups composed with nested let graph schemes

Date: 2026-09-30
Status: candidate composition theorem; reviewed within the stated pure scope; not implementation authority
Scope: one non-nested recursive SCC with pure `Var`/`Int`/`Lambda`/`Apply`/`Let` bodies and continuation
Governing records: `2026-09-30-intrusion-pure-recursive-group-adequacy.md`, `2026-09-30-intrusion-nested-let-graph-schemes.md`, `2026-09-30-intrusion-scc-constraint-scheme-rules.md`

## Syntax and outer environment

The outer semantic/generation environments may contain both monomorphic
endpoints and previously established graph schemes, related by
`Ξ≈_ηΓ` from the nested-let note. A recursive group
`G={d₁=λx̄.e₁,…,dₙ=λx̄.eₙ}` is one resolved SCC. Its bodies and continuation
may contain nested non-recursive lets; nested recursive groups are excluded.
All identities allocated for this SCC are fresh from the outer environment.

## Declarative member relation

Under fixed outer anchor assignment `η`, define `MemberTypes_G,d(Γ,η)` by
shared monomorphic recursive assumptions and separate exposed member types:

```text
Γ_S = Γ[d_j↦Mono(S_j)]_{j∈G}
```

```text
MemberTypes_G,d(Γ,η) = {
  R_d |
    ∃ (S_j,T_j)_{j∈G}, (R_j)_{j∈G∖{d}}.
      for every j∈G:
        Γ_S,η ⊢ λx̄.e_j : T_j
        ∧ T_j ≤ S_j
        ∧ T_j ≤ R*_j
}
where R*_d = R_d and R*_j = R_j for j≠d.
```

The vector `S` is shared across all member bodies, so internal recursive
references are monomorphic. `R_d` is a member's externally visible type. The
group is valid when this joint relation is nonempty. This relation permits
subsumption from each body type to both its recursive assumption and exported
type; it does not equate those values by identity.

For every member define a candidate graph scheme

```text
S_d^G = (C_G, root=r_d, Q=L_G, A=A_G)
```

where `C_G` is the complete constraint graph from the recursive-group
generation rule, `L_G` contains all SCC-created identities, and `A_G` is the
set of referenced fixed outer anchors. In this pure subcase, all group-created
identities are local in every member scheme and no separate cycle binder or
erasure set is needed.

### Group adequacy with polymorphic outer names

Fix an outer `Ξ≈_ηΓ` and a vector of recursive assignments `S`. Extend the
endpoint assignment to `η_S = η ∪ {s_d↦S_d | d∈G}`. Extend the environments
simultaneously with `d↦Mono(s_d)` and `d↦Mono(S_d)` for every `d∈G`; they
remain related under `η_S`. For each body, the nested-let expression
adequacy theorem gives:

```text
Sat(C_d,η_S|A_d,ν_d) => Γ_S,η_S ⊢ λx̄.e_d : eval(t_d,η_S,ν_d)
Γ_S,η_S ⊢ λx̄.e_d : T_d
  => ∃ν_d. Sat(C_d,η_S|A_d,ν_d) ∧ eval(t_d,η_S,ν_d) ≤ T_d
```

The added inequalities `t_d≤s_d` and `t_d≤r_d` are therefore exactly the
declarative `T_d≤S_d` and `T_d≤R_d` premises, with subsumption and transitivity
handled by the expression theorem. Distinct body-local ranges are pairwise
fresh; they combine with the one shared vector `S` and the exported vector
`R`. Hence the complete graph assignment relation is equivalent to the
declarative recursive-group derivation even when outer names are polymorphic
schemes and bodies contain nested non-recursive lets.

It follows that:

```text
Inst_{S_d^G}(η|A_G) = MemberTypes_G,d(Γ,η)
```

The application of that theorem to bodies containing `let` uses the
structural scheme-adequacy result from the nested-let note. Outer polymorphic
lookups become fresh SCC-local graph identities; their outer anchors remain
in `A_G`.

## Declarative `let rec` rule

In the declarative semantic environment, `Poly(P)` denotes a source-level set
of independently selectable member types, not a graph-scheme object. Define:

```text
ValidRec_G(Γ,η)       Γ[d↦Poly(MemberTypes_G,d(Γ,η))]_{d∈G},η ⊢ e : T
──────────────────────────────────────────────────────────── LetRec
Γ,η ⊢ let rec G in e : T
```

`ValidRec_G` means the joint recursive relation has at least one solution.
This checks every definition even when the continuation does not use it. Each
continuation occurrence of a group member may independently choose a type in
its exact `MemberTypes` set, while all such schemes retain the same outer
anchor assignment. Internal group uses remain monomorphic in the SCC bodies.
This rule is independent of `C_G`, `S_d^G`, and the generator. The graph
scheme appears only as a candidate representation whose denotation will be
proved equal to `MemberTypes`.

## Compositional generator

Under `Ξ`, allocate fresh self endpoints `s_d` and generate all group bodies
in the shared environment `Ξ_G=Ξ[d↦Mono(s_d)]_{d∈G}`. Allocate fresh exposed
roots `r_d` and form the complete group graph:

```text
Ξ_G ⊢ λx̄.e_d ⇓ (t_d,C_d)     for each d
C_G = ⋃ C_d ∪ { t_d≤s_d, t_d≤r_d | d∈G }
L_G = Identities(C_G,{s_d,r_d}_{d∈G}) \ Anch(Ξ)
A_G = Identities(C_G,{s_d,r_d}_{d∈G}) ∩ Anch(Ξ)
```

The group-scheme validity theorem gives each `S_d^G`. Generate the
continuation under `Ξ_G^+=Ξ[d↦Poly(S_d^G)]_{d∈G}`:

```text
Ξ_G^+ ⊢ e ⇓ (t,C_e)
Ξ ⊢ let rec G in e ⇓ (t, C_G ∪ C_e)
```

Every polymorphic group lookup in `e` adds a fresh copy of `C_G` with a fresh
renaming of all `L_G`; it fixes `A_G`. Thus the output includes (a) one base
copy checking that the declared group itself is valid and (b) independent
member-use copies for the continuation. The base and every use copy have
disjoint local identities and share only fixed anchors.

## Conditional composition theorem

Assume:

1. the nested-let exact scheme-adequacy theorem, including its
   `Ξ≈_ηΓ` environment relation and extensionality lemma;
2. globally fresh, pairwise disjoint local identity ranges, with common fixed
   outer anchors.

Then the `let rec` generator above is sound and complete for the declarative
`LetRec` rule, and its generated root scheme has exactly the declarative type
set under each fixed outer anchor assignment. The graph scheme's denotation
is related to the source-defined `MemberTypes` sets by the group adequacy
proof; environment extensionality connects that representation to the direct
semantic `Poly(MemberTypes)` entries in `LetRec`. The enclosing root scheme uses
`Q=Identities(C_G∪C_e,t)\Anch(Ξ)` and
`A=Identities(C_G∪C_e,t)∩Anch(Ξ)`.

**Soundness.** A satisfying assignment for `C_G∪C_e` restricts to a
satisfying base assignment for `C_G`; recursive-group adequacy yields
`ValidRec_G`. Every group-member occurrence in `C_e` has its own renamed
`C_G` witness. Parent transport and group adequacy show that each renamed root
lies in its source-defined `MemberTypes` set. The nested-let/expression
soundness theorem, with environment extensionality, then derives the
continuation under `Poly(MemberTypes_G,d)` and hence the `LetRec` conclusion.

**Completeness.** A declarative `LetRec` derivation supplies `ValidRec_G`,
which recursive-group adequacy maps to a satisfying base assignment for
`C_G`. The continuation derivation uses the source-defined member sets; group
adequacy and environment extensionality relate those to `Poly(S_d^G)`. The
nested-let/expression completeness theorem supplies satisfying witnesses for
its body graph and every member-use instance. Fresh ranges are disjoint from
the base group assignment and from each other, while all anchors use the same
`η`; combine the assignments to satisfy `C_G∪C_e`.

The proof does not multiply independently projected marginals to claim one
joint assignment across different use sites. The base `C_G` checks that the
source group has a valid recursive typing; each member scheme use then gets
its own assignment fiber, exactly as the declarative rule specifies.

## Limits and next gate

This is a compositional theorem for a custom pure declarative system, not a
proof that its `LetRec` rule captures all Yulang behavior. It assumes the
recursive-group and nested-let adequacy lemmas; it does not cover recursive
groups nested in RHSs, member-specific fetch boundaries, effects, handler
hygiene, roles, diagnostics, failure scheduling, or runtime observations. It
also does not prove the frozen Oracle's final accepted-program capability.
The next semantic gate is to compare this exact pure source envelope and
its final observations against the Oracle, then widen the declarative rules
only where Oracle characterization identifies relevant source behavior.

## Review record

On 2026-09-30, this M3 composition candidate received compiler-referee and
spec-auditor review. Review findings exposed and the primary corrected a
generated-scheme circularity in declarative `LetRec`, the direct source-set vs
graph-scheme environment interface, a non-simultaneous recursive environment
notation, and a bound set-comprehension variable. Final delta review found no
remaining concrete issue within the stated pure fixed-anchor scope. The
reviews did not assess Oracle final acceptance, effects, runtime soundness, or
implementation. This remains a candidate theorem and does not authorize
implementation.
