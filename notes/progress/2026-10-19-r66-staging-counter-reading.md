# R66 complementary counter reading: staging needs an annotated-boundary projection

Status: **candidate rule-applicability obstruction**, not a source-qualified
counterexample, semantic ambiguity, complete theorem, or source/native closure.
Author: `/root/r66_staging_counterreading`; no descendants or coauthors.
Session: `current-conversation-2026-10-19-r66`. Contract revision 1,
SHA-256 `7ee35d3d66b2acd0c5115a75e7a8125bd136df98308dfc61dbc6d205a8e433e4`.
Luna-supplied baseline `253f08169` (contract baseline parent
`64f63ff01577155b892e658c5fbeb090dd4c451b`). All 26 direct dependency
hashes matched the frozen manifest before this note was written. No Git inspection.

## Objective and smallest rule instance

The fixed source is the contract's `forward` and `outer` pair. Let `d` be the
whole-annotated definition of `forward`, `L` its original Lambda, `t` its
formal, `n=Name(t)` its body, `a_t/p_t` the formal annotation, and
`a/(p_A,p_R)` the distinct whole Function annotation. `I` is the resolved
`io` family. R64 D0–D2 establishes the lexical objects, `Gamma(t) =
Computation(E_t,Int)` with open `E_t`, the `p_t`/Name permission lineage, and
the negative `p_A` versus positive `p_R` meanings. These facts are
parametric in the original joint context; they do not construct its complete
`xi=(nu,K,D)` or the whole-annotation checking proof.

I attacked the specific proposed first step: synthesize a symbolic Lambda
operand using the selected Name and Function result rules, then check the
written whole type against it. At `n`, the selected rule
`Gamma(t)=I_t -> Synth(Name(t))=I_t` applies with
`I_t=Computation(E_t,Int)`. Its displayed Lambda/Result equation would yield
`Fun(P_t,Comp(E_t,Int))` **for an unannotated function result**. The governing
result decision explicitly limits that complete choice to unannotated results
and leaves explicit/nested result checking and its selected typed path open
(`notes/design/2026-10-02-source-result-synthesis-choice.md` §§1,4–5).
Here `d` has a whole Function annotation. Thus the cited equation does not,
by itself, discharge the rule's applicability at `d`.

The other pinned source grammar does not silently repair that step. Its
Lambda schema requires the actual role/entry, captures, **body checking under
the actual formal binding**, body consumer and complete invocation. Its
annotation/final-formation rule checks an **actual completed value** against
the written target and retains both endpoints and realization evidence
(`notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
§§3.1,3.2(6)). Build allocates local rule choices at their original scopes,
and FinalRoot publishes the actual final annotation target with preceding
evidence (§§4–5). None of those statements says that this annotated Lambda's
body-checking derivation projects to the selected unannotated Result derivation,
or that adding the whole annotation after such a projection commutes with
its original checking choices. The same grammar warns that a Lambda challenge
cannot be formed by assuming body safety (§3.1).

## Exact missing premise and falsifier

The proposed factorization needs an **annotated-boundary projection and
reassembly lemma** for this original source occurrence, not a second copy of
the already known Name rule. In schematic form, with `C` the complete
original scoped constraint/evidence graph and `A` the written Function target:

```text
for every original joint valuation/strategy xi and original typed provider v,
  Derive_checked(d,L,a; xi,C,v)
    iff exists original-scope Lambda operand U and prior evidence e such that
         Derive_Lambda_operand(d,L,t,n; xi,C,U,e)
         and Check_whole(a,p_A,p_R; xi,C,U,e,v),
with the same original coordinates, provider, checks, ordinary constraints,
result/consumer evidence and typed substitutions in both directions.
```

Any fresh auxiliary witness must be placed at its actual telescope and
transported explicitly; its incidental identifier need not match. This is a
**candidate required lemma**, not a definition of `Sol_src` or a derived law.
The first application test is whether the operand derivation can use the
selected unannotated Result clause at the *annotated* binding, or whether a
separate applicable Lambda body-check/result rule supplies precisely its
source interface. A valid owner-supplied rule and a same-context two-direction
derivation would falsify this obstruction. Simply erasing `a` to obtain an
unannotated expression changes the source occurrence and fails the test.

The context cannot be manufactured by first solving `L`: §3.4 of the source
Generalize proof requires one simultaneous component description and one
strategy on the joined tree; `exists xi. Lambda(xi)` and `exists xi.
WholeCheck(xi)` do not prove the required joint existential. Conversely,
placing the written target and its checking choices in `C` at their authentic
source owner is legitimate only after their local rule premises are supplied.
Treating desired `Check_whole` edges as already generated would assume the
conclusion. The final target's `p_A` permission cannot borrow the formal's
`p_t` licence. Positive `p_R` allowance adds no actual effect inflow. Neither
the approved expression bridge nor Direct constructs a completed operand;
the former names it as an input, and the latter consumes complete roots
(`questions/2026-10-10-source-annotation-typed-root-bridge/approved-answer.md`
q1/d1; `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
§§1,1.2).

## Scope of this result

This is a failed direct rule application and a discriminating proof obligation,
not an exhibited source program with two conflicting applicable derivations.
It does not show that staging is impossible. It leaves R65-CURRENT-OPERAND-1,
R64-SRC-ANN-ARG-1, R61-SOURCE-ASCRIPTION-FORMATION-1, original computation
forwarding preservation §§1,6–7 and Simple-sub A/B OPEN; R50 remains NOT
ADOPTED. No `Sol_src`, `Corr`, actual `Q`, `Sol_nat`, substitution theorem,
native inequality or code slice follows. If the proof lane supplies an
authentic annotated Lambda operand and the projection/reassembly lemma, this
counter reading is superseded at that exact premise, subject to independent
review.

Method: rule-domain comparison and attempted symbolic derivation, with the
fixed source as the smallest witness to the scope mismatch. Oracle
independence: no Oracle behavior, current compiler acceptance, or assumed
transition checker was used. The direct-dependency manifest was hash checked
26/26; detailed reading targeted the result law, independent source grammar,
approved annotation/permission decisions, R64/R65 premises and original
parent. Other pinned files were not exhaustively audited for global absence
of a supplier. No tests, builds, compiler execution, seeds, ranges, mutations,
Git operations or code edits were run. CPU/RSS unmeasured; wall time is
bounded by the 300-second assignment but exact runtime is unknown.

Recommended next action: the constructive proof lane should prove or refute
the annotated-boundary projection at this actual binding from an applicable
Lambda/body-result rule, then test the original same-`xi` solution equivalence.
