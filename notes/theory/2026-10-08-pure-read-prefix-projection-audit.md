# Pure-read initial/lookup prefixes: finite consumer projection audit

Date: 2026-10-08
Status: non-authoritative bounded derivation and conditional evidence countermodel; frozen on submission
Baseline: `2c7b4aaf4d3d5ff6e2bea5c3054943a250b3df59`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Independent review, representation selection, production implementation and gate closure: none

## 1. Objective and result

Audit the next consumer in [captured-step factorization](2026-10-08-captured-step-interface-factorization.md) §5: the original formation derivation retained by [ReadInvoke](../design/2026-10-08-pure-read-call-result-constructor.md) §3 before actual callee Return and argument formation.

For the fixed approved inner source `call(result(name f),result(name x))`, the explicitly expanded Name/Result/Bind/Call prefix rules have a finite typed **fact projection**, constructed below by eliminating the source derivation once at its owner. These facts include its real reference substitutions, source tags, exact roots, phase delimiters and suspended dependent interfaces. Neither the outer function definition nor an actual challenge is needed to read those projected facts at use. Finite here means finitely many dependent schemas and registered edges, not finitely many events, challenges or observations.

This does **not** prove that ReadInvoke's required original-derivation evidence factors through those facts. The selected definition retains that derivation, and no selected elimination law equates its evidence with a fact certificate. The exact remaining premise is a lawful interpretation of the retained-formation field through the proposed projection, including evidence transport. Thus the original derivation remains a required operand of the current selected constructor; it has not been proved semantically indispensable to every possible transformed export. This audit supplies a concrete candidate operand list and derives its factual consumers, rather than another transition probe assuming the missing law.

Claim classes:

- Established inputs: the selected immutable Name/Return, source prefix, IF and ReadInvoke constructors, in their stated independent interpretation.
- Bounded derivation: source-owner elimination constructs the finite fact projection and supplies the enumerated early factual consumers (§§3–4).
- Conditional theorem: full early evidence factorization follows if the retained-formation consumer law in §5 holds.
- Conditional countermodel: a proof-sensitive retained field can fail evidence factorization while all those facts agree (§6). No actual selected-source pair with that sensitivity is established.
- Open: the consumer law, finite presentation of independent transitive leaves, transformed-export selection and all later/residual inference gates.

## 2. Exact authority and original operands

The primary pinned HEAD as above. Every direct dependency in §9 equals that revision; dirty task/map/architecture records were navigation only and supply no premise. The integrated root-policy q1/a1 decisions 1–5 require the actual transformed export, additional information whose sufficiency is proved, and no use-time traversal of the original definition. Additional information and its size are undecided. This note proposes no adoption of a representation or new source meaning.

Governing sections:

| Selected source | Exact scope used |
| --- | --- |
| Pure-read result constructor | §§2–5, especially §3 initial/lookup formation and suspended fixed-domain suffix |
| Source-interface definition | §§2–4; complete source/arm placement, independent semantic validity |
| Source-interface construction | §§3.1–3.3,4–6; typed substitutions, inserted original derivations, finite registered frames and lawful actions |
| Captured closure constructor definition | §§2–4; selected Strict and finite source-prefix interpretation |
| Captured closure introduction | §§2,4.1–4.3,6; actual source Name/Result, ordered Bind, pre-Return Call and separate descriptor proof |
| Call input construction | §§3–4; Data-Name, Code-Result, Code-Call, original origins and substitution theorem |
| Contextual Function membership definition / semantic input realization | definition §§2–3; realization §§4.1–4.3; immutable binding restriction and actual pure Return |
| Source result synthesis choice / typed core | choice §§1,4; core §6 source normalization only; no general adoption of the Draft core |
| Source contracts/common allowance | §§2.1–2.2,3.2–3.3,3.7; source-image independence, admission and original alternatives |
| Captured-step boundary cut / factorization | cut §§3,6–8; factorization §§3–5; exact transformed-root and missing consumer target |
| Root-policy approved answer / receipt | accepted decision items 1–5 and integrated q1/a1 consumption |

Fix the **one original** index and assignment:

```text
j = (B,X,eta0,xi,Delta_c;
     d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
xi = (nu,K,D)                 beta = (d_f,R_f).
```

The captured f and its root/interface originate at `sigma_apply`. The inner lexical use `u_f`, checking occurrence `u`, Call c and x binding retain their actual `sigma_step` incidences. `u_f` and `u` are separate. No captured coordinate becomes fresh or eligible by projection. Let q be the genuine original source formation at these indices, and let e be an independently admitted current event with its jointly valid immutable environment. All fact/evidence readouts below share the same witness; projections cannot choose independent per-port witnesses.

The current environment supplies f's same hereditary binding certificate at `A_f`, x's actual post-entry/rebind certificate at `A_x`, and independently justified same-value inclusion at f's checking view `F_c`. Those are semantic inputs, not conclusions of source formation. The actual `Act(v_f,U_f,r_f)` is not known by a pre-Return result constructor; after Return it is supplied by same-branch Name inversion. World compatibility and live authority are independently checked at e and every later event.

## 3. Candidate projection at the source owner

Define **research notation**, not a selected new descriptor, `pi_fact(q)=b_pre` by inversion of the fixed constructor tree:

```text
q = Code-Call(q_f,q_x,t_arg,Check_c,o_c,suffix_ports)
q_f = Code-Result(Data-Name(b_f,resolve_f),o_f)
q_x = Code-Result(Data-Name(b_x,resolve_x),o_x).
```

This inversion is available at construction. A Name's source `Value` tag is retained; it is not recovered from its solved endpoint shape. x is a Value result binding after the selected entry/rebind. The suspended argument is the actual reify origin of this Call. None of this constructs a Delay value or assembles an actual challenge early.

The projection has the following **dependent** fields. Schematic evidence types name the existing original judgments; they do not introduce new permission or typing rules.

| Field | Exact operands/evidence retained | Consumer and dependency |
| --- | --- | --- |
| `original_index` | j, original binder order/dependency positions, source/operator/use origins and actual lexical-to-checking exposure | Every path and guard is interpreted at that same joint index; IF alone supplies no guard truth |
| `read_f` | Original declaration/root `(d_f,R_f)`, `Value(A_f)` source tag, local contextual slot, actual composed scoped Resolve/Capture substitution and typed use-to-binding incidence | Data-Name projection and Lemma W; same-root f obligation. Compose the actual edge chain at construction, never select a binding by endpoint equality |
| `read_x` | Actual x result-binding root and `Value(A_x)` tag, its typed original result/rebind slot and local read substitution | Future argument Name/Result readout under the actual x binding; no x exists on a pending pre-rebind step-entry branch |
| `result_f`, `result_x` | Code-Result introduction at each original result node/port, pure Return tag, same-data-to-result/provider/current-world field maps | ME-Result and Return prefix typing; never an implicit consumer or added pure layer for a Computation-tag binding |
| `call_form` | Actual Application/Gen-Call-0 origin, typed local constructor case, original callee/argument/whole-Call result slots | Pre-Return ME-Call phase placement; Application origins cannot be manufactured from printed Gen-Call-0 fields |
| `checks` | Original VIncl and whole-argument compatibility **origins**, checked F_c/R_c, complete independent D_c schema and all original emitted local constraints | Origins keep source obligations active. Same-value inclusion truth, whole-carrier typing and admission stay independent semantic inputs |
| `arg_form` | Original reify root/license **interface**, latent Name/Result interface, dependency-closed capture references, open whole-carrier hole and source-diagonal section maps | Only a suspended inert-formation obligation early; the actual later filling uses its own certificate. The field has no actual carrier or challenge |
| `bind_form` | Original ordered Bind formation, actual-result/current-C1 dependent middle telescope, rebind/result delimiter and suspension map | ME-Bind initial/administrative cases; later Return uses its actual value/C1, later raw resumption its current C' |
| `suffix` | Fixed-domain, parameterized obligation: at later actual CalRet and actual independently formed h, independently assemble d in D_c, then actual-provider receiver, receipt/entry, result and future obligations | ReadInvoke §3 suspended suffix; retain complete dependent interfaces and original proof actions. This is a schema, never a fabricated d, acceptance certificate or total returning execution |
| `if_placements` | Complete callee/carrier/receiver/result/future field maps and original contextual IF-Insert/IF-Use placements, with original parameter substitutions | Selected IF factual placement; source/checking/receiver/whole-result ports remain separate |
| `guards_actions` | Original scope/provider/hard-bound/joint/authority guard schemas and supplied lawful whole actions on every field/evidence family | Evaluation at live e/C or later e'/C'; source origin is not a live grant |
| `alternatives` | Every original P/source, W and Z clause at its original region, its complete telescope, tag, hard guard, license/domain/semantic map and output-dependent provider/future fields | Independent full contract leaves; no source anchor for Z, no W-output cast to its predecessor provider |

`checks` preserves the original independent local constraints even before satisfaction is known. The original external residual P/W/Z contracts and all capture/environment/import dependencies remain conjunctive at their original scopes. Their fields are neither discharged nor generalized by this projection. Independent source formation may exist with unsatisfiable generated constraints; it grants no world or provider existence.

The certificate must retain the actual composed typed substitutions and maps, not IDs pointing to objects that require reopening the source definition. A finite registered dependency graph can represent these local schemas without unfolding referenced provider bodies. Finiteness of arbitrary opaque leaf contracts and their lawful evidence operations is an explicit condition; the table supplies no such synthesis theorem. An atom hiding q or a closure that traverses q at use would fail this proposed projection's intended boundary.

## 4. Bounded derivation of the factual consumers

Assume genuine q; a finite source/capture/reference registration graph; complete typed schemas and original lawful actions for its independent leaves; and the selected independently valid world/binding/guard inputs at the current event. Then the table's fact projection is constructed finitely and supplies each of the following early consumer conclusions.

1. **Resolution and source role.** Invert Data-Name. In a local case retain its declared binding and typed selection map. In an imported case compose the actual Resolve/Capture substitutions through the dependency-closed original capture. Composition preserves the original same middle telescope and sharing; no new root is allocated. Read `Value(A_f)` and `Value(A_x)` from these binding conclusions. These facts establish exactly which original binding each Name refers to, without traversing its resolution proof at use.
2. **Immutable lookup and pure prefixes.** Apply Lemma W to the retained scoped binding projection at e. The independent immutable environment supplies its actual value/root and hereditary membership. The selected Return/prefix case uses that environment and the `result_f` field maps. Before completed Return, it yields only the actual code/capture/current-world incidences with no result. Upon actual Return, same-branch inversion yields the same value/provider/world. No latent component executes. These actions depend on the retained typed maps, environment and live guards, not the internal proof of their source construction.
3. **Initial/lookup Call placement.** The original Call expansion has a first leg `result(name f)` and an unreached suffix. At zero-step and administrative first-leg observations, read `call_form`, `bind_form` and the retained current phase. Their original operator maps place that prefix in the complete Call frame and suspend `arg_form;suffix`. This uses the existing source operator equations; it neither inserts receiver membership into a callee prefix nor proves DescMem from IF incidence.
4. **Suspended later obligations.** The suffix fields are the original dependent interfaces under formal actual-provider/C1 and whole-carrier parameters. A prefix can retain these interfaces without providing actual parameters. Once the actual CalRet and formation occur, their original parameter maps instantiate the same interfaces. The independent punctured context, other environment, registered hole values and whole-carrier admission then supply a complete challenge. Keeping this parameterized obligation early is finite and contains no Q or invocation-output premise.
5. **Lawful fact actions.** A supplied legal whole map acts jointly on every typed operand, source tag, original origin, substitution and evidence action. Selected IF naturality and the original substitution law give `g(pi_fact(q)) = pi_fact(g(q))` for these factual fields. The actual world/authority evaluation remains an event argument. This equation does not supply an action on a discarded proof-identity field.

The proof is one fixed constructor inversion plus finitely many actual reference-substitution compositions. It derives the local fact outputs, rather than taking a prefix coverage theorem as input. The same conditional laws hold over arbitrary independent compatible contexts and future events; there is no finite client grammar, seed enumeration or imposed domain restriction.

This result is deliberately narrower than source-image evidence factorization. Constructing ME-Result or ME-Call **from q** at the producer is already selected. Replacing the selected required q operand by b_pre at every future consumer is the separate step below. An original raw receiver observation `o_U` is not available in these early prefixes and is never invented to bridge that step.

## 5. Exact remaining evidence premise

Let `Early(q,e,O,w)` denote the existing initial/lookup ReadInvoke evidence family at the original tuple, including its retained-formation operand, not a new semantic rule. Let `FactEarly(b,e,O,w)` abbreviate only the original consumer conclusions enumerated in §4, including the suspended obligations and unchanged guards. The bounded result supplies factual readout

```text
Early(q,e,O,w) -> FactEarly(pi_fact(q),e,O,w)
```

and source-owner construction of b. It gives no evidence-equivalence in the reverse direction after q is removed.

The missing **candidate** law has concrete content: an early consumer evidence family on b_pre, whose substitution along pi_fact has lawful forward/back evidence maps to Early at every original e/O/w, preserving proof fields actually observed by later consumers and commuting with every supplied legal whole action and event restriction. The backward map may not retrieve q by opening the source or select a convenient new source/ME witness. Original independent M_E remains separate from DescMem; if a later consumer requires its finite proof, that proof's corresponding field/action must also be accounted for. This law changes no predicate by fiat.

**Conditional early-factor theorem.** If that law holds, §4 substitutes its finite actions for the early q reads. The finite IF/Bind field-composition derivation then factors the initial/lookup part of ReadInvoke through b_pre. This consumes the existing fixed source/descriptor meanings; it does not redefine M_E as `FactEarly`, select a new result descriptor or prove the complete g_step supplier.

The unresolved scope is precisely evidence interpretation of original formation, not Name lookup correctness, actual-provider admission, prefix transition consistency or another proof of finite frame allocation. Finite source syntax alone does not establish that interpretation; an evidence family may retain more than its judgment's proposition. Conversely a nominal storage of q alone proves no necessity of source traversal. Both overclaims are excluded.

## 6. Minimal conditional countermodel and discriminators

No actual pair of different genuine derivations of this fixed approved Call with identical table fields was found or claimed. Source uniqueness may make some fibers singleton; it has not been proved by these sources. The following is a **conditional evidence countermodel**, testing the exact extra premise rather than claiming a competing Yulang meaning.

Assume there are two original formation witnesses q0 and q1 at the same j whose projected facts are equal. Add the **unestablished countermodel premise** that an evidence consumer observes their distinct original-formation identities, and that compatible evidence transport must preserve that identity. Use one fixed e/O/w: the zero-step body-Call prefix after completed x rebind and before CalRet. No W/Z branch, challenge witness, actual Delay, request, receiver receipt or returned provider is involved. Extend the evidence interpretation by retaining a nominal original-formation token:

```text
pi_fact(q0) = pi_fact(q1) = b
RetainedFormation(qi) = {token_i}
identity_readout(token_i) = qi, with q0 != q1
compatible transport must preserve identity_readout.
```

All §4 factual predicates and maps can agree. A transport between these singleton evidence families changes the observed identity and therefore fails the extra identity-preservation requirement. Equivalently that required readout is nonconstant on the pi_fact fiber and cannot be a readout of b alone. Mere absence of a previously supplied transport would not prove impossibility: the observed unequal readout is the discriminating premise here. Making that readout irrelevant and supplying a lawful token equivalence removes the obstruction. The countermodel uses two tokens because a singleton fiber has no such obstruction; it uses one prefix because later execution is irrelevant. It is a logical model of the **missing evidence law**, conditional on a duplicate fiber and the extra identity consumer, not proof that the selected interpretation possesses those tokens or that ordinary execution can distinguish them.

This identifies an independent discriminating review obligation: determine the actual original Early evidence projections; if none reads proof identity and their complete actions are exactly §4's fields, derive the required evidence maps from those existing clauses. If a field does read it, retain its precise finite certificate or exhibit a genuine source-indexed separating pair. Do not invent proof sensitivity or proof irrelevance as language meaning.

Two simpler omission controls show why a shapes-only export cannot replace the proposed fields:

- Deleting the `Value`/`Computation` source tag permits result(name f) versus designated consumption of a computation-tag name at equal solved runtime shape. The selected normalization A distinguishes them; the proposed b retains the tag. This control ranges over the selected source grammar, not two versions of the fixed approved inner Value source.
- Deleting the actual typed binding/reference substitution permits an unrelated same-endpoint root to replace captured `(d_f,R_f)`. Data-Name and the original IF use then fail at the fixed use. This is an invalid-certificate mutation, not a second admitted source execution or a reason to freshen f.

Neither control falsifies full b_pre. No executable mutations were run; larger toy transition counts would leave the retained-evidence law untouched.

## 7. Boundaries at the transformed export

The proposed b_pre is a local typed fact certificate, not the whole `apply` definition or a renamed full source relation. Its suspended suffix retains the approved complete receiver/result/future schemas, including independent alternatives; it does not retain source execution of arbitrary f or h. Whether all transitive contracts have an adequate finite declaration and whether any evidence field secretly requires source traversal remain open and must be checked before choosing it as export information.

All independent compatible punctured contexts, nonreturning/effectful whole-carrier fillings and the exact D_c domain remain. On the source diagonal, actual Delay(Name x) supplies its own carrier formation later. Open fillings supply their independent port formation, license and complete carrier certificate. Same-provider membership elimination occurs only after independent challenge formation. P/source, W-image and unanchored Z alternatives remain distinct, with actual roots, witnesses, final guards, domain/admission laws and actual output-provider future contracts. A whole-Call alternative is not routed through this early structural prefix.

Original residual constraints and joint `nu,K,D` remain at their original binder/source scopes. One legal incoming-use action must preserve their correlations together with all certificate fields, fixing the transitive captured/environment/import closure. Generalize emission, scope eligibility, joint hiding, Direct resolution at actual g_step, all-view extension, full H-factor and production/lifecycle correspondence receive no closure here. Literal current ReadInvoke construction still retains q until its interpretation law is supplied; no unauthorized semantic substitution has been made.

## 8. Checks, resources and recommended next action

Method: construction-owner inversion and dependent field elimination, followed by a minimal conditional evidence-fiber countermodel. This is a different method from supplying a transition checker or repeating the static IF allocation proof. The actual missing premise is class A evidence preservation and class D retention/projection debt under compiler-engineering; no new annotation or source restriction is justified.

No independent operational oracle was used. The derivation shares the selected source rules, primitive contracts and lawful actions with ReadInvoke. A checker assuming those transitions could verify certificate shape or finite consistency; it would not establish the source laws or the retained-formation evidence interpretation. No test, build, executable experiment, search seeds/ranges, randomized mutation, network lookup, child, Git mutation or other output path was used. Only sequential lightweight reading, hashing and note-integrity checks were performed. CPU/RSS were not measured; no numerical process/RAM/wall-time budget was supplied in the assignment. No heavyweight process ran. Finite-presentation claims are structural and conditional, with no source-size resource bound asserted.

Checks at freeze: every direct dependency equals pinned baseline bytes; `git diff --check -- <leased path>`; local Markdown relative-link existence; no trailing whitespace; SHA-256 of the frozen leased file. These are integrity checks, not independent review or mechanized proofs. Shared dirty files were preserved. Truncated early read captures were followed by narrow governing-section reads; no repository-wide absence claim or exhaustive consumer inventory beyond the selected constructor cases is made.

Recommended next action: give an independent closure reviewer the frozen note and selected ReadInvoke/source-prefix clauses, and require actual forward/back evidence maps for the retained-formation field through the enumerated certificate, or an exact additional original evidence projection that prevents them. Do not launch another equivalent prefix transition probe.

## 9. Dependency snapshot and commit packet

Every path below matched baseline bytes at capture. Historical hashes quoted within the dependencies are not substituted for these hashes.

| Direct input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-captured-step-interface-factorization.md` | `3e68f03311dffd892433e1d99b5f7f77a1d162df72bedef95b67474d1a5210fd` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `notes/theory/2026-10-07-call-input-construction-proof.md` | `f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/design/2026-10-02-source-result-synthesis-choice.md` | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/theory/2026-10-08-captured-step-finite-boundary-cut.md` | `4eaeb482aaf23d42809a8253a3e755ef7105395be711f7c94dce9d900fe53f45` |
| `questions/2026-10-08-successor-generalize-root-policy/approved-answer.md` | `e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5` |
| `questions/2026-10-08-successor-generalize-root-policy/receipt.md` | `c3bb6fbab0e3ba431fca56b4b7cdca54278d66a3711eb47bf8b9f9a812322a42` |
| `crates/yu-hir/src/shadow.rs` | `5a3c61bf87a3f6147897816beea369df49059a49141607af9cca8c720c43386f` |
| `notes/progress/2026-10-06-shadow-call-source-occurrence.md` | `ceb54a7d0bbcf1d95a9752034b7f9eb744ff68ff1214d8fed65e89e7babe5a19` |

The production source-occurrence owner is HIR's `ApplicationSourceOccurrence` and its `Skeleton::application_source_occurrences()` accessor: it retains only existing expression/position/source-form/callee/argument IDs. The inspected accessor and its reviewed crosswalk explicitly supply no source role, typed Call view, proof or semantic admission. It therefore does not already implement b_pre. No compiler change is proposed in this lease.

Commit packet:

- Exact leased/changed path: `notes/theory/2026-10-08-pure-read-prefix-projection-audit.md` only.
- Baseline SHA: `2c7b4aaf4d3d5ff6e2bea5c3054943a250b3df59`.
- Dependency changes: none at capture; final revalidation/hash supplied in the handoff. Branch movement alone requires only direct-dependency revalidation.
- Claim/review status: non-authoritative bounded fact projection and conditional evidence theorem/countermodel; no independent review, full-factor closure or production authority.
- Checks already run: baseline-byte/hash comparison, scoped whitespace check and local-link validation; final frozen SHA-256 supplied in the handoff.
- Proposed checkpoint message: `research: audit finite pure-read prefix consumer projection`.
- Shared-record deltas left for primary/curator: record the enumerated source-owner fact certificate and the exact retained-formation evidence law still open. Do not close H-factor, change ReadInvoke meaning, promote a representation, or alter canonical DAG/theory status on this note alone. Task/index/authority/question files remain untouched.

The producer stops writing before submitting this artifact for frozen review.
