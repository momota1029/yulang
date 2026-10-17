# Operation fixed-c specialization at the complete output

Status: Draft semantic candidate, revision 1; independent review NOT_RUN; not adopted. No production authority.
Assignment: `NPAIR-OPERATION-FIXED-C-SPECIALIZATION-20261018`; author `/root/npair_fixed_c_candidate`, sole author, descendants 0. Requested Sol/high; observed effective model/effort UNKNOWN/UNKNOWN.
Sprint: `npair-operation-rule-completion-and-accepted-replay-20261018`, contract SHA-256 `e9ea1ebb5db72ebcf7348e512206a1b39b8e60232d2bff5459f0bc394f7526f0`; supplied baseline `9f23cfe84`. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original conditions closed **0 -> 0**.

## 1. Target and exact change from the prior proposal

Fix the original declaration `p`, its actual `Prim(alpha,m_q)` clause, typed `Ref(t,m_v)` at `v`, one lawful joint `theta`, and the complete original `Sigma_theta=(A_theta,B_theta,Lambda_theta)` and `xi=(nu,K,D_original)`. Keep the original scope tree, all phase, response/current-state, raw-continuation, provider/future, guard, admission and license binders in `Lambda_theta`. Fix the original contribution **c at its actual source formation before observations**, together with its original formation witness and independent license. The parent quantifies over the original admitted whole primitive witnesses `w:Prim_alpha(h,y;xi)`, all relevant observations, futures and R/W/Z alternatives at these original binders. This note neither chooses a new `c` after `y` nor changes that quantifier order or the admitted source domain.

The target is the original c's occurrence at positive Written `s1=Operation.Function.ResultValue.Function.ResultEffect`, operand occurrence `j`. Root intrinsic Self at `s0=Operation.Function.ResultEffect` is a different field. `?e_Op` in the pinned original-c audit asks for the same-c occurrence, original field license and dependent `eta_c : occurrence contributes-to L_out[s1,j]` at the *actual complete* declaration output. Its `contributes-to` relation is the existing input to adopted negative-pair L2; it is not defined by this note.

The previous OC-Written proposal has a sound conditional calculation for a fresh `OperationWritten(q)` and a complete output. The adoption decision correctly observes that a disjoint fresh constructor does not act on the already-fixed original c. The candidate here changes the proposed semantic interface: it attaches an occurrence-indexed **selection certificate to the original c's own formation**, then adds a same-c output rule. It never forms `c_q`, casts an old c into `OperationWritten(q)`, or identifies c by family/row/native member. This is a proposal for an original Operation specialization, not a claim that current original rules already contain it.

## 2. Formation selector and full dependent data

Let `d_form` be the source semantic introduction of the *already fixed* original c under the actual primitive declaration/reference and theta. This is an input, not a witness reconstructed from a typed result or native row. Define a proposed source-owned selection judgment with the following exact payload:

```text
q = (p, alpha, actual clause and registration t, Ref(t,m_v) at v,
     joint theta, complete Sigma_theta and original binder/scope tree,
     b_out, s1, j, a, ell_field, kappa_c)

kappa_c : original formation proof of this very c at p/v/theta,
          with a local Operation-introduction provenance and its original license
b_out   : original binder of the complete declaration output after A_decl
(s1,j,a,ell_field) : actual positive Written operand occurrence and independent
                     field-license reference in B_theta under b_out.
```

The declaration's actual complete type proof supplies the field's syntax and binder placement; it does not supply c's attribution. `ell_field` is a reference to a separately valid license at that source occurrence. Its dependent instantiation must be proved at each final output. Two equal operands at distinct source positions retain two different `(s1,j)` occurrences; a tail and all later-lower checks remain in their own fields. A graph back edge remains a reference, not an unfolded new occurrence. The family projection is not inverted to recover theta or local binders.

The proposed **Op-Fixed-Select** rule is a partial, formation-time rule:

```text
d_form : original formation of c at the actual p/v/theta
kappa_c : source-owned local Operation introduction of that same c in d_form
q.field : independently licensed positive Written (s1,j,a) in B_theta at b_out
SameOwner(kappa_c,q.field) : original declaration/reference/field-origin check
---------------------------------------------------------------- Op-Fixed-Select [NEW]
sel_Op(d_form,q) : Selected_Op(c,q)

elim_sel(sel_Op(d_form,q)) = (c,d_form,kappa_c,q,SameOwner).
```

`SameOwner` compares full source introduction, reference, joint theta, binder and occurrence; it is not family equality or an assumed output incidence. The original semantic owner must give this source-owned selector a real constructor or computation over its `Prim_alpha/T_alpha` formation. Merely postulating `Selected_Op(c,q)` would rename `?e_Op`. The rule is deliberately *partial*: an original c from an inherited operand, root Self, a tail, or another constructor does not qualify by shape. If such a c is nevertheless within the parent's fixed-c quantifier, this candidate fails to cover that case; the source domain cannot be narrowed to hide it. No uniqueness of c across distinct fields is imposed. If one original c can genuinely cover two positions, retain two selection proofs and their separate occurrence/license lineages; if two c values have the same family, retain both identities. The same `sel_Op(d_form,q)` is fixed for every later admitted observation and complete output.

This selector is the first **new semantic assumption** unless the original owner supplies an existing `kappa_c`/`SameOwner` derivation at these precise indices. The inspected generic IF-Insert/IF-Use rules transport a supplied primitive projection; they do not create it. The source owner must not make selection depend on an output provider, successful comparison, handler match, Permission, subtraction, solver query or future observation.

## 3. A_decl output action and the proposed eliminator

At an authentic returning source development retain the response/current-state evidence `d_resp`, *entire* ordered suffix `k0 >>= A_decl` and the actual complete `A_decl` development `d_A`. The reviewed Operation construction has `k0(r_resp,Cnow)=Return(r_resp,Cnow)`, but this equality ends **before** `A_decl`. Its actual complete output is `out(d_A)=(r_out,Cout)`, which may differ from `r_resp,Cnow`. Open the independently established complete `B_theta`/result typing proof `beta_out` at `b_out` and `Cout`. If `A_decl` changes the result interface, use its genuine whole typed map into this B interface; shape similarity gives no cast. Define by structural elimination:

```text
sigma_out = the original dependent output-binder/world/future substitution in d_A
phi_out   = field_projection(beta_out, suffix(s1,b_out), j)
lambda_out : original ell_field transported and valid at sigma_out, final scope,
             provider/world/future and admission domain
g_out      : original final G, K, D, guards, authority and licenses

act_A(sel_Op(d_form,q),d_resp,d_A,beta_out,lambda_out,g_out)
  = OpFixedWritten(c,q,d_resp,d_A,b_out,r_out,Cout,
                   s1,j,a[sigma_out],phi_out,lambda_out,g_out).
```

`field_projection` reads the returned Function's `ResultEffect` suffix relative to `B_theta`'s output binder. It returns the actual operand and its dependent future/provider, tail, constraint and field typing data. It does not execute the returned Function, emit a dynamic request or assert contribution incidence. The typing and substitution equations, *when their full source premises are supplied*, are derivable existing eliminations. `lambda_out` is not inferred from c or phi alone; it requires the original license's actual whole dependent action. A missing output certificate, changed-interface map or license action is a missing original premise, never a new refusal of an originally admitted witness.

The proposed **Op-Fixed-Out** rule supplies the semantic attribution missing in the old derivation:

```text
sel_Op(d_form,q) : Selected_Op(c,q)
d_complete : admitted complete Operation development at this same p/v/theta
d_resp,d_A,out(d_A)=(r_out,Cout),beta_out,phi_out,sigma_out as above
lambda_out and g_out : genuine original dependent license/final-domain evidence
---------------------------------------------------------------- Op-Fixed-Out [NEW]
eta_c = OpFixedWritten(...) : the original occurrence (s1,j,a[sigma_out])
                              belonging to this SAME c contributes-to L_out[s1,j]

elim_out(eta_c) = (c,d_form,kappa_c,q,d_complete,d_resp,d_A,
                   b_out,r_out,Cout,s1,j,a,sigma_out,phi_out,
                   lambda_out,g_out,complete original witness lineage).
```

The conclusion is an extension of the original c-indexed incidence judgment unless an existing original source rule is independently shown to derive precisely `eta_c`. It is not a theorem from `phi_out`. Its computational elimination retains the full witness and never returns just a family, point, row or endpoint. The fixed `c,q` work for **every** genuine complete output `d_A` in the original fiber: the rule computes `sigma_out`, `phi_out` and dependent license separately at each output. It never chooses c from a successful output. A pending Request retains the raw suffix and suspended field contract; it has no `out(d_A)` and receives no returned-output `eta_c`. A later genuine Return may use the rule then. Divergence retains every finite original prefix without an eventual-return premise.

## 4. R/W/Z, whole maps and preservation burden

Keep the original `H_G(R)=least X. G(y) and (R(y) or Z(y) or exists x,z. X(x) and W(x,y,z))` with its **complete** Sigma/Lambda/G and all original evidence. The proposed specialization must be lifted by induction on its actual finite derivations, with the original fixed c and selected q retained. This table is a set of required case laws, not evidence that opaque W/Z constructors already supply them.

| Original case | Candidate action and proof still needed |
| --- | --- |
| Returning R | The rule above uses actual `d_resp`, complete `d_A`, `beta_out`, final G and dependent license/domain. It cannot substitute `r_resp` for `r_out`. |
| Requesting, pending or divergent R | Preserve the current state, event and original ordered raw suffix, response contract, admission/future checks and finite prefix. No output action before an actual return. |
| W preserving indexed coordinates | Retain the original predecessor, W witness, c, q and final G. Even equal coordinates need a genuine original W action for the occurrence, license and full future. |
| W changing provider, world, scope, field or live admission domain | At the *new* output binder require W's original whole typed map `M_W`, transformed `beta_out`, field/license action and separate domain/admission map `D_W`. Prove the square `back_y(M_W^+(eta_x)) = M_W^old(back_x(eta_x))` on full c-indexed evidence and consumer lineage. A field absent under a changed interface is an unsatisfied case, not a reason to drop y. |
| W changing declaration/interface | Require an original whole interface map from q's p/v/theta/B to the new one, including identity of c, occurrence, license and all dependent future coordinates. No family/shape cast. If original W allows a case without this map, candidate coverage is open or false. |
| Unanchored Z | Use Z's *own* original declaration insertion, complete whole tuple/output proof, same-c selection or lawful identity-preserving map, original license, final G and independent future/domain action. It cannot borrow a predecessor, request event or R source execution. |
| Union, Conjunction, Bind, Call, consumer | Retain true branch tags; both conjunction proofs at one original tuple; ordered dependent middle and actual complete Call witness. A CallMem witness for another c is not the selected c. |
| Scope, Rename, Ref, recursion | Act at the original binders by one lawful whole substitution over c, q, Sigma/Lambda, licenses, incidence and futures. Actual reference placement and finite graph derivation remain. |

Every original permitted witness must lift and forget to the **same entire** witness, not only its projected observation. Each added incidence must reflect to genuine old incidence if a conservative-completion claim is desired; every old incidence must remain. Original active consumers require both forward and back laws at their real input indices. Whole injective rename may commute by the existing typed substitution law when all fields are supplied; extrusion, identification during Value-SCC-qualified intrusion, hiding/generalization and W/Z changed-domain actions need separate genuine laws. The proposal adds no early solved-provider precondition and no source restriction to make these cases easy. Source shape, final G or positive membership by itself does not prove a domain action.

The proposed induction computes `lift_R(d_R)=act_A(sel,d_resp,d_A,beta_out,lambda_out,g_out)` only on returning R. For a genuine W edge `z:x->y`, `lift_W(sel,eta_x,z,M_W,D_W,beta_y,lambda_y,G_y)` uses its final whole tuple, typed map and independent live-domain map to construct `eta_y` for **the same c**; the commuting square above is its required eliminator equation. For a genuine unanchored Z witness `z_y`, `lift_Z(sel,z_y,beta_y,lambda_y,D_Z,G_y)` introduces `eta_y` from Z's own complete output and placement, again with the formation-fixed c and no R predecessor. These are proposed rule signatures. Their concrete original `M_W,D_W,Z` formation and license bodies are unavailable, so an abstract invocation of either signature is not a completed proof of the original quantified case. Pending versions retain the original continuations and do not call `lift_R/W/Z` until a complete output exists.

## 5. Consumer applicability, consistency and falsifiers

At the adopted negative-pair route, genuine `eta_c` can be composed with the actual two result-child Function comparisons to form the L2 incidence derivation `delta` at the exact negative `D_alpha` occurrence. Only an ordinary reached lower yields `At(D_alpha,w,delta)`; Permission is separate and creates neither lower nor residual. `N-Transport` must preserve this *same* c and derivation through accumulation, Function propagation, `R1 -> Install(g) -> Capture -> whole FreshUse -> g()/J2`, levels, extrusion, qualifying intrusion and generalization. `N-Subtract-Elim` still requires the real demand, source/receiver scope and use instance, original selected consumer/removal evidence and all future checks. The received fixture has no Catch, so this candidate predicts no subtraction there. F1 remains the complete finite frame/image inventory; FK1 independently covers foreign continuation application and transport. One local `A_decl` action does not discharge either universal quantifier.

For every actual original active Contrib/Inc/Cover or removal consumer `U`, define the *required comparison* at an unchanged complete input `I` (same c, q, p/v/theta, world, provider, license, demand, use, other contributions and future):

```text
app_old(U,I) iff app_new(U,lift(I));
selected_old(U,I) = back(selected_new(U,lift(I)));
residual_old(U,I) = back(residual_new(U,lift(I)))
```

The equality is proof-relevant: it includes selected contribution and residual lineage, retained lowers/checks, tails, scopes, suspension and invalidation, not just row contents or a Boolean. Conversely every candidate consumer derivation must reflect to an original one on the same input. This is an obligation against the *actual* semantic consumer rules; no generic erasure theorem supplies it. The old primitive/consumer interface currently exposes no such reflection. A newly true `eta_c` may make an original incidence-sensitive consumer applicable where it previously was not, so source execution equality is insufficient for consistency.

Concrete falsifiers and discriminators:

1. **Selector failure:** provide one originally admitted, source-qualified Operation formation with fixed c and a genuine target Written `(s1,j)` whose c-form witness has no `kappa_c`/SameOwner case, or whose only case is Self, imported, tail or another declaration/reference. That refutes universal coverage of this specialization. Missing inspected rule bytes alone do not establish such a witness.
2. **Output/action failure:** provide a complete admitted `d_A` whose actual output/provider/world/field/license cannot instantiate the proposed action, including a changed-interface W or unanchored Z. The original witness must be retained, not excluded. Two equal-family Written positions or a responder/final-output mismatch expose an invalid cast.
3. **Conservative-equivalence failure:** provide genuine old evidence `not I_old(c,d)` at one admitted complete output, the candidate's `eta_c`, and all other premises of a real incidence-sensitive consumer `U`. Then `app_new` is true while `app_old` is false. This is the previously established **conditional** one-output discriminator; no old negative-incidence proof or real consumer instance is supplied here. A differing selected residual despite equal acceptance is another falsifier. Unknown old incidence is never a negative proof.
4. **Source/native failure:** a mismatched source position/view/member j, reference/theta, output binder, copied use, or separate semantic witnesses merged by one native endpoint refutes a proposed correspondence. A transition test that assumes `eta_c` cannot authenticate source emission.

For existing-spec impact, Op-Fixed-Select and Op-Fixed-Out would extend the original Operation `Prim_alpha/T_alpha` interpretation and its c-indexed `Contrib/Inc` meaning, potentially changing active consumer applicability and residuals. Their syntax and output erasure do not establish compatibility. The prior decision explicitly withheld adoption; this candidate does not supersede it or the authoritative inference/Call/negative-pair contracts. If source owners establish that the selector and incidence are already derivable original rules, this candidate becomes an elimination proof under those exact rules. Otherwise it needs semantic authority, independent review and a compatibility or explicit change decision before implementation. The fresh `OperationWritten(q)` option remains disjoint and cannot serve as that existing-c proof.

## 6. Source/native boundary and direct parent application

The pinned source audit and bounded current source read locate `candidate_operation` at the actual declaration signature/value link, `candidate_signature_value`'s intrinsic family only at the pointer-identical root Function, and the nested Written field through `candidate_signature_effect`'s positive Support(view). `candidate_check_effect_operand` expands Support to `AnnotationMember(view,j)` and an actual tail; its Allowance branch checks an AnnotationMember or separately allocated Contribution. `prepare_candidate_fresh_use` remaps member views while retaining j and has a distinct Contribution arm. `candidate_signature_view` records Operation provenance and does not create annotation source weight for it. These are represented source/native fields, not an emitted original semantic `Selected_Op` or `eta_c`. A native member/family/row cannot invert to c or merge separate semantic witnesses. The semantic path through actual N-Ingress/At, N-Transport and N-Subtract-Elim remains independently unproved.

**Application to unchanged parent:** if the source owner derives `sel_Op` for the already fixed original c and proves Op-Fixed-Out is an *existing* original rule at every actual complete output, `?e_Op` can be filled by `elim_out` and fed into L2's authentic comparison derivation. The parent then still needs all original alternatives, active consumer reflection, full route/Replay, C1/C2, F1/FK1, P3/P4/P5/P6, complete Call, soundness, principality and termination. On current evidence the selector and same-c attribution are new assumptions, W/Z/domain and consumer laws remain open, and original closure stays **0 -> 0**. This candidate is a falsifiable specification for the missing rule, not proof that old semantics contains it.

The minimal later **provisional** code TODO is `OC-NATIVE-WITNESS-CORRELATION-20261018`: only after an approved semantic rule and exact Luna lease, correlate an actual `Selected_Op`/`eta_c` proof with the authentic emitted Support/AnnotationMember at `(source position,j)` and its complete output/FreshUse lineage. Its falsifier is any c, reference, theta, provider/world/scope, binder, occurrence, license or copied-use mismatch. No synthetic Contribution atom or assumed-transition fixture satisfies it. This note authorizes no compiler edit.

## 7. Reuse, remaining owners and boundary

Reused within their premises: the reviewed conditional OC-Written complete-output calculation, original IF placement, Operation's actual `k0`/`A_decl` spine, complete result typing when supplied, adopted negative-pair L2 route, and the one-output conditional consumer discriminator. Rejected as proof of old semantics: a fresh disjoint c, family inversion, root Self as Written s1, typed field phi as contribution eta, response/final-output equality, Permission as inflow/removal, record erasure as consumer reflection and a test of assumed transitions. Prior authors retain their headers: `/root/npair_operation_source_contract` (formation proposal), `/root/npair_original_formation_compatibility` (decision), `/root/npair_original_c_proof` (fixed-c audit) and `/root/npair_original_formation_falsifier` (discriminator). This author cannot independently certify the combined result.

Exact requests returned to Luna: **OC-ID** — original Operation `Prim_alpha/T_alpha` owner must supply or decide the source-local c selector at p/v/theta and same-c output incidence, with full complete Sigma/Lambda and field license; falsifier 1 or 2. **OC-ALL** — primitive W/Z/future/domain owners must give concrete all-alternative actions and changed-domain laws; falsifier 2. **OC-CONSUMER** — original Contrib/Inc/Cover and actual removal owner must prove forward/back applicability and result parity at unchanged full inputs; falsifier 3. **OC-NATIVE-WITNESS-CORRELATION-20261018** — later provisional implementation owner only after semantic approval; falsifier 4. These are evidence requests, not new leases. No third equivalent assumed-transition proof should replace the missing source-owned selector. A genuinely supplied selector/eliminator is the next in-envelope mathematical input; semantic adoption or enlarged inputs return to Luna.

Checks: read-only governing/source inspection and SHA-256 comparison; no tests, builds, Cargo, compiler command, Git mutation, external contact, nested CLI or children. Exact dependency and resource receipt is in the paired frozen handoff. Review pending; writer stops after handoff hashing.
