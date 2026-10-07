# Local O0 under the user-selected original Call formation definition

Date: 2026-10-07
Baseline: `d3def26c1079566bc4bd7660e2a21ddcfe960530`
Status: Reviewed; local O0-selected theorem closed in the stated emitted-record scope
Claim class: local theorem under the selected formation definition
Scope: actual emitted Gen-Call-0 records; exact approved nested source
Authority input: [adopted original formation definition](../design/2026-10-07-original-call-formation-definition.md),
  user selection at `2026-10-07T22:09:13+09:00`, 「承認するよー．定義にしちゃっていい」
Reviewed-by: independent compiler-referee, no findings; definition/approval conformance independently reviewed by spec-auditor
Implementation / production authority: none
Review record: [adoption integration](../progress/2026-10-07-call-construction-proof-review.md#7-approved-definition-and-local-o0-integration)

## 1. Result and definition boundary

The user selected the two uniform formation definitions in the reviewed
[construction proof](2026-10-07-call-occurrence-construction-proof.md) §10,
including its §10.1 exact-root interpretation, as the governing previously
unspecified original cases for **actual emitted Gen-Call-0 records**. Write
`T_call^sel` for precisely that selected fragment. This note takes the user's
selection as authority input, now recorded in the linked narrow Authority;
it records no broader approval. The producer used the exact published
definitions and direct decision; the primary later added this authority link.

Under this definition, the local O0 producer is available: it constructs the
exact immediate signature position, an original typed source occurrence and
its typed output correspondence at every such record. It also proves the
exact semantic root equation and legal whole-tuple substitution coherence.
The historical statement that these cases were unadopted is no longer a
missing premise for this selected fragment. The result is not a theorem that
the historically unspecified judgment was already derivable from unchanged
rules, or an identification with a separately fixed older position family.

This proof specializes construction Theorems 1, 2, 6 and 7 by the selected
definitions. No `kappa`, typed occurrence, successful comparison, complete
profile, seed truth, semantic Call typing or source execution is assumed.
The sole source input is the existing well-scoped emitted record inventory,
including its old generator premises. General record generation is not proved.
No canonical DAG node is promoted by this producer note.

## 2. Exact inputs and statement

Let `Generate0(D)` be a finite well-scoped input in construction §5.2's
already stated envelope, with its frozen emitted inventory `E_D`. Fix
`e in E_D`, and retain its entire dependent index:

```text
Idx(e) = (B,X,xi,Delta_e;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
xi = (nu,K,D)                     beta = (d_f,R_f)
U_e = F_e : FunctionDemand         rho_e = demand(e)
```

`d_f,A_f,R_f` are the original declaration/endpoint/shared-root indices;
`u_f` is the resolved callee Name and `u` the distinct upper checking
occurrence. `Delta_e` is the actual local demand context, retaining all
imports and dependencies. A symbolic declared Function demand is not a
satisfying descriptor. `rho_e` retains the demand/root/provider/context
indices specified in construction §4.4 and contains no desired `p0`
correspondence, occurrence witness, comparison result or execution.

**Theorem O0-selected.** In `T_call^sel`, for each `e in E_D`, construct:

```text
H_eff(rho_e)                      independent signature formation
q_e = inv_eff_orig(rho_e)
    = outEff_orig(U_e)
    = Inv(Id(U_e),U_e)             at rho_e's exact dependent fiber
ce_e = CallEff_orig(e)            original typed Call-effect occurrence
kappa_e : TypedOutputCorrespondence_orig(
            U_e,outEff_orig(U_e),e.p0;
            B,X,xi,Delta_e; beta,u,c)
```

The correspondence retains the original source/shared-root incidence and
separate `ElimOrigin` leg to `p_out(c)`. Its underlying one-port graph is
`{(q_e,e.p0)}`. Construction is total on the emitted inventory even when its
generated relation is inconsistent. For every legal sorted assignment in
§10.1's unchanged complete-description domain, its exact root realizes the
existing full complete-invocation interface. All dependent projections commute
with each legal whole-tuple map in construction §7. These conclusions require
neither a satisfying generated strategy nor an execution witness.

## 3. Construction, typing and all projections

Invert `e`'s actual Gen-Call-0 construction. It declares `U_e` in `Delta_e`
and supplies the original source fields. Construction Theorem 1, specialized
to selected `Sig-CallEff`, registers the independent Function frame and proves
`Id(U_e)` a walk and `Inv(Id(U_e),U_e)` an effect position. This derives
`H_eff` and the exact `q_e`. No step reads `p0` to form the signature.
Root immediate-position uniqueness excludes result-latent, body-only and
native-return positions; endpoint equality cannot change the constructor tag.

Apply selected `OC-CallEff` to `e`, `rho_e=demand(e)` and that exact `q_e`.
The result `ce_e` inhabits the selected original typed occurrence family.
Its eight eliminators, specialized from construction §5.1, are:

| Eliminator | Computed result |
| --- | --- |
| `sig(ce_e)` | `q_e=outEff_orig(U_e)` at the exact demand fiber |
| `src(ce_e)` | `e.p0=(beta,call.effect)` |
| `upper(ce_e)` | `e.u`, the original upper checking occurrence |
| `call(ce_e)` | `e.c`, the actual source Call |
| `staticRoot(ce_e)` | `(e.d_f,e.R_f)=e.beta` |
| `sourceScope(ce_e)` | `e.Delta_e` |
| `sourceOrigin(ce_e)` | the complete original resolved/generated dependent record |
| `invocationLeg(ce_e)` | `e.ElimOrigin`, retaining `e.p_out(c)` |

The original static root/position formation required by O0 is supplied in
two steps. First, inversion of the **actual Gen-Call-0 derivation**, not of
a bare tuple of labels, yields its scoped `R_f` declaration at the original
`d_f,A_f` and the resolved shared-root/capture provenance retained by `e`.
For the nested instance, formal registration and the same-root Name import
provide this provenance at `sigma_apply` and `sigma_step` respectively.
Second, selected `Sig-CallEff` forms a position in exactly that dependent
root/provider fiber, and selected `OC-CallEff` forms its original typed
source incidence there. Its `staticRoot` and `sourceOrigin` eliminators retain
that derivation's root and origin. Thus `q_e` inhabits the selected static
signature-position fiber and `ce_e` its typed source-occurrence fiber at
`beta`, with that provenance; no
original position is obtained by casting the pair `(d_f,R_f)` itself.

Eliminate this **typed constructor** to obtain its dependent incidence
certificate `kappa_e`. This is the `TypedOutputCorrespondence` port identified
by [minimal clause](../progress/2026-10-07-original-call-output-minimal-clause.md)
§§1,3 and §7, now supplied by the selected definition. Forgetting its evidence
gives the graph above; forgetting is not the introduction proof. Source/root
formation here means this constructor's typed static incidence at the original
registered root. It does not prove semantic provider membership or a complete
`SharedContract` interpretation merely from that root's registration.

The [P2 attack](../progress/2026-10-09-original-assoc-p2-constructor-attack.md)
table combines original root/position interpretation with introduction of a
member into `Slots(beta)`. The selected definition supplies the static
Call-effect interpretation just proved. That table's original slot inventory
and slot-member introduction are still O1, not an extra field of this local
O0 certificate. No full original root-domain interpretation is claimed.

Construction Theorem 2 applies these two definitions once to every member of
the supplied inventory in its original order. Calls with empty inventory
retain their old node and child evidence, adding no local `ce_e`. No missing
record is manufactured from a Call-shaped node. This proves the stated totality
and gives exactly construction Theorem 7 in `T_call^sel`. QED.

## 4. Exact semantic realization

Use selected §10.1, over any independently interpreted old complete-description
domain and its existing full `ExecuteCallable` interface. Let `eta` be any
legal sorted assignment there, and let `d=interpret_old(eta,U_e)`. It need not
satisfy the generated source constraints. Define `J_call(d;xi)` exactly as
§10.1: the whole parameterized old relational interface, with actual entry,
body, designated consumers, native-return delimiters, complete executing view
and unchanged admitted joint dependencies. It is not one chosen trace or an
outward support row. Typed-core §§3,9 give the interface data used here.

The selected root definitions give, at the jointly interpreted indices:

```text
interpret_sel(eta,q_e)
  = interpret_sel(eta,Inv(Id(U_e),U_e))
  = Inv_sem(Id_sem(d),d)
  = completeInvocationEffectPosition_sel(d)

interface(interpret_sel(eta,q_e)) = J_call(d;xi).
```

The first equality uses `Sig-CallEff`; the second uses the selected two root
evaluation clauses; the third and the interface equation use the source-free
`SemFrame_call(d)` definition. This is §10.1's reviewed realization proof
specialized to `rho_e`. It uses neither `ce_e` nor `p0` nor comparison success.
The descriptor, captured provider/root and locally dependent context all use
the same `eta`; none is interpreted under a separately chosen assignment.

This discharges minimal-clause §7's exact root realization requirement in
the **user-selected** original case. It supplies no evaluator for unrelated
original paths and no common-model, descriptor/admission inhabitance or
semantic Call typing theorem. If the sorted assignment domain is empty,
the universal equation makes no existence claim. A bridge to a separately
fixed historical root evaluator would still require construction §9, but
that bridge is not a premise of O0 in the selected case.

## 5. Whole-tuple substitution and preserved reduct

Let `theta` be a legal uniform map of construction §7: it acts once on the
whole original binder graph, `B,X,xi`, declarations, endpoints, source tags,
dependent records and incident evidence, fixing required rigid imports.
Construction Theorem 6 specializes to:

```text
theta(rho_e) = demand(theta(e))
theta(q_e) = Inv(Id(theta(U_e)),theta(U_e))
           = inv_eff_orig(demand(theta(e)))
theta(ce_e) = CallEff_orig(theta(e))
theta(kappa_e) = kappa_(theta(e)).
```

The last equation follows by constructor elimination on `ce_e`: the same map
acts on both typed incidence legs and every index. In particular `staticRoot`,
`sourceScope`, `upper`, `sourceOrigin` and `invocationLeg` commute, with
`theta(p_out(c))` retained in the last leg. This proves the exact §7 occurrence
and signature substitution laws. It does not independently freshen `K,D`,
providers or any per-port witness. Noninjective endpoint substitution does
not identify distinct tagged paths or source/checking occurrences. Inverse
reflection is asserted only for legal injective renamings on their image.

Construction Theorems 3–5 apply to this canonical static representation's
unchanged generated predicates and executable reduct: erasure changes no
old binder/conjunct/strategy/instruction/transition operand. Thus old generated
solutions and old execution observations are preserved, including empty
solution sets. These theorems do not prove preservation when a future consumer
uses occurrence facts to introduce new admission, profile or owner clauses.
Legal-map coherence also does not discharge arbitrary graft/hiding validity,
generalization eligibility or complete source generalization.

## 6. Exact nested source instance

For `my apply f = { my step x = f x; step }`, use the approved structural term:

```text
lambda(f, bind(step,
  result(lambda(x,call(result(name f),result(name x)))),
  result(name step)))
```

Construction §7 already calculates its actual singleton emitted record `e_c`.
Instantiate §§2–5 above with that record. Registration anchors `d_f,A_f,R_f`
at `sigma_apply`; the captured `u_f` reuses that same provider/root inside
`sigma_step`. `U_c=F_c` stays in its actual `Delta_c`, including local `A_x`
where required. The derived `q_c`, `ce_c` and `kappa_c` live at this inner
demand while retaining the outer root as an import. The source `p0`, lexical
`u_f`, generated upper `u`, Call `c` and `p_out(c)` remain distinct indices.

Bind and final `result(name step)` retain this static evidence and return the
closure inertly; neither adds a second Call occurrence or executes `f x`.
The singleton count is the count of constructed Call-effect occurrences
for this emitted inventory, **not** a count of `Slots_orig(beta)`.
Reviewed [S1](../progress/2026-10-06-directional-joint-source-judgment.md)
§3 separately derives the exact seed-stage upper protection. O0 uses no seed
truth; joining S1 later must retain its original `k,v,u_f,u` incidences and
scopes, with no lower/provider back-protection or inferred actual role.

## 7. Exact consumer substitution

Suppose a consumer has a proof `P(h0,hrest)` whose `h0` is precisely this
original typed output-map/formation port at `e`'s indices. In the selected
fragment ordinary proof substitution forms
`P(kappa_e,hrest)` (with `H_eff,q_e,ce_e` supplied if separately exposed).
The residual `hrest` is unchanged. The index match uses the entire dependent
record; it is never an endpoint cast or an identification of `u_f` with `u`.

| Direct consumer / exact locator | Port now constructible | Residual not discharged |
| --- | --- | --- |
| [Round-5 output introduction](../progress/2026-10-07-original-call-output-introduction-round5.md), constructive cut; minimal clause §7 | Independent signature formation, exact immediate `q_c`, original typed occurrence and its output incidence | Any stronger full original signature interpretation beyond this selected case; general source record production |
| [K-Owner](../progress/2026-10-07-successor-original-kernel-construction-round2.md) §3.2 | Its `TypedOutputCorrespondence(U,outEff(U),p0; scope tree,xi)` premise, instantiated with `U_c,e_c.p0` | K-Owner itself remains a proposed original owner introduction; its Resolve/Capture/SharedContract, annotation/seed/exposure/upper facts retain their own meanings. S1 supplies the selected seed route only. No `s,o` is constructed here |
| [Round-4 exact fiber inputs](../progress/2026-10-09-original-call-fiber-construction-round4.md), O0/O1 table and conditional completion | The O0 static output/root-incidence input for this emitted record; consequently the O0 argument of its O1 package | O1 original Slots/Own introduction, C0 full admitted-inlet typing, C1 original preimage/Emb, J0 joint incidence and uniform coverage |
| [Source-introduction contract](../design/2026-10-07-original-call-source-introduction-contract.md) §§3–6 | Its O0 row and O1's typed-map argument, within the selected emitted-record domain | O1/C0/C1/J0, complete original witnesses, attachment/licensing, admission, source adequacy, production conformance |
| [Round-6 Theorem C cut](../progress/2026-10-07-original-call-theorem-c-output-map-round6.md), exact withheld map; [constructive round 5](../progress/2026-10-07-original-association-constructive-round5.md), typed-`p0` grant | Replace the isolated typed output-map grant with `kappa_c` | Their complete decorated source, owner/view kernels, local laws, receipts, actual input derivation and other maps remain supplied inputs |

For Theorem C / [C-realization](../design/2026-10-05-source-contracts-and-common-allowance.md)
§3.5 and [source-indexed realization](../design/2026-10-04-source-indexed-callback-realization.md)
§2, this removes only the local supplied-map obligation where it is exactly
the O0 port. Their full decoration envelope is not obtained from `ce_c`.
Likewise typed-core §6 Normalize may consume designated computation-port
typing beyond this static effect correspondence; O0 does not supply that
entire judgment. K-Image's complete `TypedOriginalImage` and K-Incidence's
`TypedOriginalSourceImage` are not identified with `kappa_c`.

No additional field of the displayed **local O0** interface is absent:
the exact demand/signature fiber, source/shared-root static incidence,
upper occurrence, local dependency context, separate elimination leg,
root realization and coherent whole-record substitution have all been supplied.
Semantic SharedContract/provider validity, full path inventories and original
owner/view membership are broader hypotheses retained by their consumers;
they are not silently included in, or discharged by, this local O0 claim.

## 8. Reviewed remaining-clause update and freeze checks

Accepted canonical remaining-clause scope:

> At the selected captured Call, O0 is supplied for its actual emitted
> Gen-Call-0 record by the user-selected §10 formation definitions, including
> §10.1 root realization and whole-tuple substitution. Keep the local demand
> at sigma_step and the captured root at sigma_apply. The next unsupplied
> original owner branch is O1 Slots/Own introduction at that same typed upper
> incidence. C0 complete admitted-inlet typing and C1/J0 original contribution,
> joint incidence and complete-family coverage remain separate; aggregate
> ORIGINAL_ASSOC/SIG_RULES/ATTACH/licensing/PROFILE and cutover stay unchanged.

Source dependencies are the linked frozen clauses; construction §§4–7,10
are the proof dependency, and the older consumer clauses locate exact ports.
All seventeen source dependencies checked by the producer matched the supplied
baseline byte-for-byte before writing. Core hashes:

```text
fbfbe797cb4843ab9d76c9e0b2191872935079f82c427147219416bdebf766b0  construction proof
0b883c273bf5ce7e413cf18463cc12b6383e1ebd3a4a917c3af8b77b683136a4  minimal clause
34434edd9d81d470b8ec355dfb94d40e7da076f8e6f003644e7840118756797e  output introduction round5
7c725904d12996c05bf6fbdceb81ee1e5e300af542fc0ecd9fc556d0fad02fa6  source-introduction contract
daa802bcf61695845718f669c1d35bfd101d2b61d49607ea8c8de82dee662910  kernel construction round2
2d55271aaaaa5d4af7b912116fa3299431bc10cc16926118767182695b2c4977  exact fiber construction round4
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  Gen-Call-0 construction
```

Method: documentary/math specialization, typed constructor elimination and
proof substitution. Checks: bounded source reads, read-only baseline byte
comparison, final dependency revalidation, relative links, whitespace and
line count. One lightweight command process at a time; zero executable
probes, compiler/code/test changes, Cargo/Oracle runs, children or Git mutations.
The independent compiler-referee passed the mathematical specialization and
exact consumer substitutions at frozen SHA-256
`83c82c19ac9bdb54349f1d99a798356c223715029310b2e8866c15c611c944dc`.
The primary accepted the report and synchronized authority, task, index and
DAG navigation. Subsequent changes to this file are status/provenance links;
the theorem statement, definitions, proofs and consumer table are unchanged.
