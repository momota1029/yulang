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

## Retained-q source corollary

Take the singleton group `G={f=λx.(x f)}` in an empty outer environment. The
syntax-directed rules allocate a monomorphic self endpoint `s`, a lambda
parameter endpoint `q`, an application result endpoint `v`, and an exposed
root `r`. The body graph and group edges are:

```text
q ≤ Fun(s,v)
Fun(q,v) ≤ s
Fun(q,v) ≤ r
```

The first inequality is the application constraint: `x` is the callee and
`f` is its argument. The remaining two are the body-to-self and
body-to-exposed-root obligations. This directly exhibits the source
constraint on `q`; no polarity-only projection is used by the declarative
member relation.

Assume the pure carrier has a greatest element `Top`, `Fun` obeys ordinary
contravariant argument subtyping, and `Top` is not a subtype of any Function
type. Also assume `Bottom` is least.
The candidate member relation excludes `Fun(Top,Bottom)`: if
`Fun(q,v) ≤ Fun(Top,Bottom)`, Function subtyping gives `Top ≤ q`; combined
with `q ≤ Fun(s,v)`, transitivity gives `Top ≤ Fun(s,v)`, contradicting
properness. In contrast, the polarity-erasure graph transformation replaces
the `q` occurrence in `Fun(q,v)` by `Top`, removes the selected application
obligation `q≤Fun(s,v)`, and retains the transformed body-to-self/root edges
`Fun(Top,v)≤s,r`. It admits root `r=Fun(Top,Bottom)` by assigning
`v=Bottom` and `s=Top`. Thus this declarative source corollary reproduces the
concrete graph-level root-relation conflict without using the Oracle scheme
as the meaning of `LetRec`.

The recursive group itself is valid in the candidate relation: choose
`q=Bottom`, `s=Top`, `v=Bottom`, and `r=Top`; then `Fun(q,v)≤s`,
`Fun(q,v)≤r`, and `q≤Fun(s,v)` hold. Yet an external use requiring this
member to have a type below `Fun(Int,U)` has no candidate member type when
`Int` is not a subtype of any Function type: `Fun(q,v)≤R≤Fun(Int,U)` implies
`Int≤q`, and then `Int≤q≤Fun(s,v)`, contradicting the disjoint-outer-form
assumption. This models the final type-level rejection of `f 1` while
allowing a valid recursive definition; it is not a whole compiler or runtime
acceptance theorem.

The corollary assumes the stated pure preorder laws and the singleton
recursive-group rule. It does not interpret latent effect coordinates, prove
that the frozen Oracle accepts/rejects every corresponding complete program,
or establish the full supported-envelope theorem.

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

The retained-q source corollary was separately reviewed by a compiler-referee
and spec-auditor. They confirmed its pure singleton derivation after the
primary added the least-`Bottom` premise, explicit root assignments in both
witnesses, and the exact hypothetical erasure rewrite. The delta review found
no remaining issue in that corollary; it did not assess effects, the complete
Oracle pipeline, or implementation.

## Follow-up Oracle final-acceptance audit (2026-10-02)

A read-only compiler-referee audit compared the theorem's scope with the frozen
Oracle ledger. It found no concrete final well-typed acceptance mismatch within
the stated pure `Var`/`Int`/`Lambda`/`Apply`/`Let`/one-SCC envelope. This is
absence of a recorded counterexample, not evidence of envelope-wide
equivalence: the theorem proves generation adequacy for its custom
`RecGroup`/`LetRec` rules, while the Oracle ledger contains only finite source
observations.

The missing bridge is a two-way relation between those declarative rules and
the Oracle's final acceptance path, including source lowering, per-member
fetch/root projection, and latent effect coordinates that exist even on
syntactically pure functions. Existing probes support isolated facts: an
unproductive mutual SCC with independent uses is accepted, and the
`pub f x = x f; f 1` path is rejected. They do not characterize the complete
member relation or its use fibers.

The next discriminating fixture pair is the singleton `pub f x = x f` with
separate external uses `f (\\z -> z)` and `f 1`, compared at final check and
the selected use-root relation, then paired with the existing two-member
independent-use witness. The candidate graph admits the identity-function
use under the documented Top/Function carrier assumptions; its Oracle outcome
is unrecorded. No tests or Oracle commands were run in this audit.

### Frozen Oracle source-path follow-up

A read-only source trace of the frozen `a58eefc3` path found that the recursive
self reference in `pub f x = x f` is a local monomorphic self endpoint, not an
SCC `UseResolved` edge. External references to `f` do pass through component
quantification and receive independent per-use scheme freshening. The frozen
`dump-mono` rejection of `f 1` occurs later: specialization solves the
concrete use signature and then rejects the definition body when `int` is
used as a function. Thus the recorded finalized scheme and the final
specialization outcome are different observations; neither alone establishes
the candidate `RecGroup` relation's complete acceptance fibers.

The source trace also found that ordinary `check` summarizes inference
diagnostics without the same mono specialization gate. The recorded material
does not establish terminal `check`/`run` behavior for the rejection example,
and it does not establish the outcome of `f (\\z -> z)`. The discriminating
pair must therefore be compared at the actual final well-typed-program gate,
not inferred from `dump-poly`. This keeps the pure SCC source-adequacy bridge
open. No compiler, test, or Oracle execution was performed.

This follow-up reinforces the selected research direction: model source
typing/evaluation and per-use interfaces in one declarative relation, then
derive SCC transport and finite solver bookkeeping from it. Local self
endpoints, quantifier events, root projections, and specialization checks are
Oracle pipeline facts to compare against that relation, not semantic
constructs to copy into it.

### Identify the user-facing final gate

Further read-only CLI tracing distinguishes three gates. `check` stops after
`check_poly_from_entry` and reports inference diagnostics. `build` and default
`run` use `build_control_from_poly_output`, which first requires runtime-ready
poly output and then calls `specialize_with_runtime_evidence_and_source_provenance`
before control lowering; default `run` selects the Evidence VM backend. The
explicit `run --interpreter` path instead calls `specialize_mono_program` and
executes the mono runtime. Thus `dump-mono` is not the sole final acceptance
path, and an inference-level `check` result is not sufficient evidence for
runtime-build acceptance. The `f 1` mono rejection does not establish the
default build/run result without tracing that specialization path or running
the source through it. The next Oracle comparison should state which public
acceptance gate it targets and distinguish build/default Evidence VM from the
optional mono interpreter. This is source-path characterization only; no
compiler or Oracle execution was performed.

### Final-gate observation for the identity-function use

Using the already-built executable in the frozen `a58eefc31` worktree, with
`--no-prelude`, I queried a temporary source file containing
`pub f x = x f; pub main = f (\\z -> z)` directly:

```text
target/debug/yulang --no-prelude dump-poly /tmp/yulang_intrusion_fid.yu
target/debug/yulang --no-prelude build /tmp/yulang_intrusion_fid.yu
target/debug/yulang --no-prelude run /tmp/yulang_intrusion_fid.yu
```

`dump-poly` exited 0 and printed `f: any -> ['a] 'b`, `main: never`, and
`main` as a runtime root. Both public `build` and default `run` exited 1 in
runtime-evidence specialization with
`open2 -[never, open1]-> open0 <: unit`, pointing at the recursive `f` use in
the body. This establishes the actual standard final-gate result for this
fixture; the earlier `dump-mono` observation was not used as a proxy.

The temporary checkout was at the frozen commit but had local trace and test
changes. I inspected the production-source deltas in the inference and mono
runtime modules: they add only environment-gated diagnostics, and no trace
environment variables were set for these commands. The executable was
prebuilt in that checkout; no checkout files were changed during this query.

The candidate pure recursive-group relation has a satisfying assignment for
the same source. Let `Top` be greatest and `Fun` obey contravariant argument
subtyping. In the group constraints
`q ≤ Fun(s,v)`, `Fun(q,v) ≤ s`, and `Fun(q,v) ≤ r`, choose
`q = Fun(Top,Top)`, `s = Top`, `v = Top`, and
`r = Fun(Fun(Top,Top),Top)`. The recursive constraints hold. Instantiate the
inline identity lambda at `Fun(Top,Top)` and the external `f` use at `r`; the
call constraint holds by equality. Operationally, the call evaluates to
`id f`, then to the `f` closure, so it terminates without a request.

This is a concrete candidate-versus-Oracle final-acceptance mismatch inside
the pure one-SCC fragment: the custom declarative relation admits a terminating
pure use that frozen Oracle build/default-run rejects after successful
inference. The candidate derivation relies on its pure source/group rules and
the stated `Top`/`Fun` laws; source-language adequacy and Oracle-wide
principality are still unproved. If those rules are adopted, the compatibility
impact is to accept this additional well-typed program at build/run; the
inference dump already succeeds on Oracle. This records a precise candidate
compatibility delta, not an authoritative decision to change the source
contract. No tests were run; these were direct CLI queries against the
prebuilt frozen-worktree executable.
