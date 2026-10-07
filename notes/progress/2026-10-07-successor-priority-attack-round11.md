# Successor priority attack — round 11

Baseline for the semantic audits: fetched remote commit
`6187ed18e83e93fa0548cbb92a85bb0a1f54bfd4`. The integration worktree was
advanced to `ee2f22c04af762a4229f5b3d2dc943df8584c968` by the separately
reviewed round-10 shadow test before these reports were integrated. At the
semantic baseline the canonical DAG had 90 nodes / 196 edges: CLOSED 7,
CONDITIONAL-CLOSED 20, OPEN-PROOF 43, OPEN-SEMANTIC 19,
IMPLEMENTATION-ONLY 1. No semantic status changed.

## CALL_TYPE: actual-provider argument checking

The bounded last-rule attack isolates the post-CI-Operands cut. Given one
retained actual `CalRet(d_f,f,U,C1;w_f)` and the source Application's complete
whole-argument checking derivation, the missing interpretation must preserve
that original provider, `xi`, scopes, incidences, and witness while jointly
producing argument typing at actual `C1` and compatibility with the actual
`CarrierContract(U)`:

```text
for every retained CalRet(d_f,f,U,C1;w_f),
  source whole-argument checking derivation,
  one original joint operand witness and prior CI-Operands premises
-------------------------------------------------------------------
exists compatible w1 >= w_f preserving the same facts:
  Typed_X(Result(I_a),n_a,C1;w1)
  and ArgCompatible_X(Result(I_a),CarrierContract(U);w1)
```

The expression “post-CI-Operands cut” matters: CALL_TYPE already has the
upstream joint C0 Env/Name/Return introduction. This result does not claim an
unconditional minimum or make the two conclusions one indivisible premise.
Argument adequacy and actual-provider compatibility are distinct, jointly
preserved obligations. Checked membership for the same returned `f` and a
complete checked-to-actual Function-carrier eliminator are one sufficient
route to compatibility; universal carrier inclusion is not shown necessary,
since an argument-specific compatibility proof might suffice. Typed-core §6
identifies the Application shape only; its non-Authoritative draft was not
used to establish semantic soundness. Current HIR/solver retain the unresolved
application premise and no reviewed source constructor supplies the required
interpretation. CALL_TYPE remains CONDITIONAL-CLOSED.

Independent compiler-referee review passed after narrowing “minimum” to this
granted-operands/retained-provider cut and separating the sufficient carrier
eliminator route from necessity. No admitted-source counterexample or
Authority-consistent alternate semantics was found.

## ORIGINAL_ASSOC P2 and P3

The reviewed conditional interface for P2 makes explicit that its rule head is
not yet supplied. Fix the same original `X`, binder tree, `xi=(nu,K,D)`, and
scope. Keep the outer captured root and seed/exposure at `sigma_apply`, the
locally dependent call demand at `sigma_step`, lexical use `u_f`, and checking
occurrence `u` distinct. Given a generated Call-demand record, its independent
O0 occurrence evidence, linked seed/exposure evidence, a complete independently
typed inlet presentation, and original port/stage/scope maps preserving the
same provider and joint assignment, the missing constructor would have to
produce one original `OriginalAssocType_X` witness with certified slot,
ownership, contribution, embedding, and incidence projections. This is an
output interface for the existing judgment, not its definition or an adopted
rule. The complete presentation and embedding must cover the full original
`F_C`, not only the source `Delay(Name_x)` diagonal.

P3 has a conditional same-witness route: first obtain one original
association `a`; only then range over every required family member `z` of
that same complete presentation/contribution. If the embedding and family
projection supply each member without changing `a`, `c`, or the shared scoped
assignment, and the original coverage eliminator applies, reuse `a` for all
`z`. The weaker order `forall z. exists a_z` gives pointwise coverage only.
The source introduction, embedding and coverage eliminator remain
unestablished; observation-specific associations would still need an
independent assembly rule. Attach and licensing remain separate.

Independent spec-auditor review passed with these quantifier and scope
clarifications. No semantic rule was adopted, no real counterexample was
found, and ORIGINAL_ASSOC remains OPEN-SEMANTIC.

## REC_DESC route comparison

For one fixed original member/provider/incidence and common independent guard
bundle `G`, let `D_i` be actual ordinary descriptor membership and
`Q_i = forall h in Adm. exists e in E_h. L_i(h,e)`. Given the finite-history
premise `G => Q_i`, the restricted reflection implication
`G and not D_i => not Q_i` is classically equivalent to direct introduction
`G => D_i`. Negation retains the exact quantifiers:
`not Q_i = exists h in Adm. forall e in E_h. not L_i(h,e)`. Without `G => Q_i`
the equivalence fails. Memberwise existential extensions cannot replace a
joint extension when the original binder tree requires shared coordinates;
the reviewed FH route retains the simultaneous compatibility requirement.

Direct two-closure construction is nearer the approved finite source
construction, but this is a route-priority inference, not a weaker proven
obligation or a semantic decision. Its unresolved rule head is: actual two
constructor spines and complete invocation relations, independently
established inlet/root/world/local guards, and lawful joint witnesses at the
original binder tree must soundly introduce both ordinary descriptor
memberships. The first missing input is the independently interpreted
exhaustive returned-Function/root clauses and actual original binder tree;
cyclic evidence acceptance remains unproved. Reflection instead needs the
ordinary constraint failure to yield one independently admitted history that
defeats every legal extension. Neither route closes REC_DESC.

Independent compiler-referee review passed the quantifier equivalence and
open status, with the joint-witness qualification retained. No complete
Authority-consistent alternative or admitted-source counterexample was found.

## Status and next actions

The DAG validator still reports 90 nodes / 196 edges: 7 CLOSED,
20 CONDITIONAL-CLOSED, 43 OPEN-PROOF, 19 OPEN-SEMANTIC,
1 IMPLEMENTATION-ONLY. These attacks reduce the exact unproved rule heads but
do not close or reclassify a node. No broad tests, builds, or measurements
were run for the read-only semantic reports.

The default-off shadow lane separately starts a parameter-to-historical-row
capture from the exact HIR parameter recipe to its actual solver startup row.
It carries identity only; it must not imply successor eligibility, binder
ordering, source denotation, or Apply typing. See the focused implementation
checkpoint after review. Production inference remains unchanged and cutover
remains prohibited.
