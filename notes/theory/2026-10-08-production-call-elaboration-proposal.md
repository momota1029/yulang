# Candidate production Call elaboration at the `f x` seam

Date: 2026-10-08
Status: Draft, non-authoritative research proposal; frozen for review at handoff
Scope: a source-directed formation/constraint contract, with an exact nested `apply`/`step` instance
Baseline: `4288e155e76f23c74263cf3e0023463a3f393b3b`, `research/simple-sub-intrusion`
Exclusive write lease: this file only
Independent review: initial frozen artifact received batched spec-auditor/compiler-referee review; accepted directional-protection omission repaired; repaired delta awaits independent review
Production implementation, test, DAG-closure and cutover authority: none

## 1. Objective, authority and claim classes

The objective is to make the proposed production Call seam reviewable: identify what formation must retain before comparing a callee, specify symbolic obligations for the whole argument and complete invocation, and expose the unresolved inference decisions. This is a construction proposal, not another shadow-solver experiment. The rules below do not select a solver or new carrier. Symbols for semantic propositions are not implemented solver atoms.

The following governing sections were read. Their original force remains distinct.

| Source | Exact governing scope used here |
| --- | --- |
| [Inferred Function views](../design/2026-10-05-inferred-function-call-views.md) §§1–5 | Authoritative shared source contract, stable slot/profile, provisional protected Handler, scoped ordinary-value resolution, annotation-local permission, Q independence; detailed inference rules remain open. |
| [Directional protection addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md) §§2–4 | Current explicit user-selected upper-use output-effect protection, no backflow to an existing lower/provider occurrence, separate occurrence/seed identity, and event-to-profile evidence boundary; representation details remain Draft. |
| [Nested source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md) §§1–4 | Authoritative meaning of this exact sequential block, inert final closure, lexical capture; broader local polymorphism/brace semantics remain open. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6–7,9 | Reviewed conditional Draft construction: source tags, Result/Normalize, actual entry, complete invocation and joint containment. No wholesale adoption of the Draft follows. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2–3.7 | Reviewed conditional independent kernels, emission/admission/transport, Option 2 abstraction; concrete exhaustive production grammar unselected. |
| [Original formation](../design/2026-10-07-original-call-formation-definition.md) §§1–7 | Adopted OSig-Demand/OC-CallEff only on actual emitted Gen-Call-0 records; full source Call result remains distinct. |
| [Contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md) §§1–4; [input realization](2026-10-08-call-semantic-input-realization.md) §§3.1–3.2 | Selected same-actual-provider realization, independent checked challenges, acceptance and complete observation obligations; independent kernel/whole-carrier checking retained. |
| [Source-interface definition](../design/2026-10-08-call-source-interface-definition.md) §§1–4; [IF construction](2026-10-08-call-source-interface-construction.md) §§2–6 | Selected complete contextual clause/root/use placement and finite static source frames. Genuine primitive typing, actual-provider dispatch and admission laws remain inputs. |
| [Captured-closure definition](../design/2026-10-08-captured-closure-constructor-definition.md) §§1–5; [closure construction](2026-10-08-captured-call-closure-introduction.md) §§2–4,6–8 | Selected Strict, exact constructed F_step, Step/Block/OuterTrace, under exact independent captured-value/checking/domain/guard/arm inputs. |
| [Pure-read result definition](../design/2026-10-08-pure-read-call-result-constructor.md) §§1–6 | Selected R_c=ReadInvoke for immutable Name callee and identity complete result; unrelated/computed result checking remains open. |
| [Callback delivery](../design/2026-10-03-callback-context-delivery.md) §§1–3 | Authoritative literal B and independence of receiver role from parameter entry; actual existing callable role is preserved. |
| [Earlier skeleton ledger](2026-10-08-apply-step-core-skeleton-ledger.md) | Historical bounded skeleton. Its supplier-gap language is refined by the newer IF/closure selections above; it is not evidence that those now-selected constructors are still missing. |

The five integrated approved answers for function-call-view-formation/a2, nested-block-function-source-realization/a1, production-function-denotation/d1 (Option A), production-function-bound-membership/d1 (Option 2), and production-function-inlet-context-domain/d1 were read. Their current approved-answer bytes equal the pinned HEAD versions. No pending bundle is consumed as authority.

**Established results reused:** the selected IF formation theorem and selected Step/Block/OuterTrace within their published scopes. **Conditional derivation:** §6 below composes the source skeleton with these results under the explicitly listed hypotheses. **Candidate assumptions/choices:** C1–C8 in §7, wherever this proposal fills an unselected inference seam. C5 incorporates the already selected directional protection boundary; that boundary is not a candidate alternative. **Bounded characterization:** the shadow inequality and retained identities are implementation evidence only. This note establishes no new unconditional source-adequacy or principality theorem.

## 2. Formation before comparison

Write `Γ; B,X,Δ,ξ ⊢src e ⇝ (I_e,d_e,n_e,L_e)` for a proposed elaboration result, where `ξ=(ν,K,D)` is one joint original assignment and `L_e` retains source formation/incidence records. C1 proposes this packaging; the source forms/indices and selected constructors give its required contents. `n_e=Normalize(I_e,d_e)` explicitly consumes Result(I_e); constructing it does not execute it.

For an actual resolved application `c=(e_f e_a)`:

```text
ResolveApplication(c,e_f,e_a,owning-declaration,Δ)
Γ;B,X,Δ,ξ ⊢src e_f ⇝ (I_cf,d_cf,n_cf,L_cf)
Γ;B,X,Δ,ξ ⊢src e_a ⇝ (I_a,d_a,n_a,L_a)
actual original Application/registration/capture/entry origins
independently typed complete declaration interfaces and lawful actions
---------------------------------------------------------------- FormCall [candidate orchestration C1]
L_c = (source-call identity c; ordered child identities;
       original current scopes and joint ξ;
       callee-result dependent provider/current-world slot;
       whole carrier t_c=Delay(n_a) at its authentic reify origin;
       actual producer/entry/body/consumer/return schema at that provider;
       result/current-world/future-provider slots; all original arm slots;
       lexical/checking/annotation occurrences and constraint origins)
I_c = Computation(E_c,A_c)
d_c = reify(call(n_cf,n_a)); n_c = Normalize(I_c,d_c)
```

The IF constructors supply the full static frame on their actual source/contract envelope. They allocate a dependent *schema* for the provider returned by the callee, not a chosen runtime provider. Actual callee evaluation must precede argument-carrier/challenge assembly and receiver entry. The formation record neither claims that those events happened nor that any symbolic solution exists. `L_c` retains suspended interfaces before Return. A callee that diverges has no manufactured actual provider or argument receipt.

Here I_cf/d_cf name the callee expression interface/data, distinct from the outer I_f carrier interface and Gen-Call-0's original declaration d_f used below. Use IF-Insert at each actual clause insertion and IF-Use at each actual root reference, retaining the entire declared interface and all original alternatives, including opaque/unanchored W/Z. Keep original licenses; contextual placement grants none. Dependent future fields refer to the arm's actual returned provider, including providers absent from the source's finite list.

For an authentic emitted Gen-Call-0 `e`, retain the original

```text
Idx(e)=(B,X,ξ,Δ_e; d_f,A_f,R_f,u_f,u_x,c,u,U_e,β,p0,p_out(c),ElimOrigin)
β=(d_f,R_f)
```

and apply the already adopted OSig-Demand/OC-CallEff. Lexical `u_f`, checking `u`, receiver-output root, full Call result and elimination leg remain distinct. Neither `L_c` alone nor a raw list of matching IDs supplies an emitted Gen-Call-0 derivation. C2 leaves the all-source record-emission rule open. Calls lacking such a record retain their child evidence/old derivation under the existing authority; this note adds no annotation or rejection requirement.

## 3. Symbolic obligations and complete invocation

Given the formed source contract `F_c` and its independent whole-carrier interface `I_arg(F_c)`/challenge domain `D_c`, propose retaining the following obligations at the same source use. C3 is their proposed constraint package; the named relations have semantic meanings and still need an effective sound/principal presentation.

```text
J_f = Result(I_cf)                   J_a = Result(I_a)  [WHOLE computation]
CalleeResultCallable(J_f,A_f,F_c;L_c,ξ)
VIncl(A_f,F_c;same-decorated-value and actual-provider action)
WholeArgCompatible(J_a,I_arg(F_c);original receipt/paths/guards,L_c,ξ)
J_full = OrderedCall(J_f,Delay(n_a),ActualExecuteCallable;L_c,ξ)
CompleteResultCompatible(J_full,Comp(E_c,A_c);L_c,ξ)
```

`CalleeResultCallable` retains the callee computation's result obligation; it does not silently consume a latent value until it becomes callable. `VIncl` acts pointwise on the same decorated value, including all alternatives. Membership at F_c is the selected contextual realization: for each retained actual `Act(v,U,r)`, every independently admitted complete checked challenge is actually accepted by U and every complete/pending/zero-step/administrative/resumed/future observation meets the complete F_c contract. A convenient alternative provider cannot be chosen after callee Return.

WholeArgCompatible cannot be replaced by `A_a <: parameter-payload`, nor by checking only a returning observation. It retains inert formation, designated execution, request/response/raw handle/future families, original scope, current-event guards and original shared dependencies. In the source diagonal `t_c` is the actual Delay(n_a); in the independent open hole the filling has its own complete carrier certificate. That filling is not required to be this source's Delay or to return.

`J_full` includes callee effects and ordered receiver effects. `ExecuteCallable` includes the actual receipt, actual entry, body, designated result consumer, native return delimiters and invocation return; a separately admitted adaptation retains its real placement. For Value entry:

```text
receipt;
Force_I(actualWholeCarrier) >>= (a,r_a,current_C).
  typed-rebind at that same tuple; body; designated consumer; invocation-return
```

Retained computation entry binds the same carrier without this entry Force. An operation's native returned request thunk still needs its declaration-derived result consumer after native return. No provisional inference seed chooses the actual entry. Requests keep their raw handle and only the unfinished suffix at resumed live state; receipt is not replayed. A pure body can have an effectful or diverging complete invocation. Consequently E_c is neither an invented row union nor the lambda body effect alone.

For the selected immutable Name callee/identity result, use `R_c:=ReadInvoke(F_c,D_c,IF_c)` directly. This already selected descriptor supplies the complete staged result case under its original inputs. For a computed/effectful callee or an independent unrelated result descriptor, retain CompleteResultCompatible as open; C4 proposes no extrapolated descriptor rule.

Reject `callee <: Function(argument,bottom,empty,result)` as a production rule. It retains neither Result(I_a)'s full computation nor actual role/entry, typed incidences, current world, complete pending invocation and all production alternatives. Even a successful current shadow query supplies none of those source formation facts. Merely replacing bottom/empty with fresh variables would still omit these obligations.

## 4. Provisional formal refinement and annotation-local permission

C5 proposes that each relevant source component allocates **one** symbolic formal/use contract cell at the registered original formal. Its internal inference state is separate from source annotations, printed schemes and runtime callable roles. The component includes declarations, definitions, uses and required recursive references; no per-use independent witness replaces that sharing.

For the approved unannotated `apply f x = f x` pattern and the exact captured nested counterpart, propose these staged evidence rules. Retain seed identity `k`, shared inferred variable `v`, original scope `sigma` and upper-use occurrence `u`; the selected Dir-Protect step is distinct from the candidate SeedFormal/RefineFormal connective rules:

```text
resolved unannotated higher-order formal b_f in this source component
---------------------------------------------------------------- SeedFormal [C5]
Seed(k,b_f,v,F_shared,provisional-Handler,
     original annotation-absence/source-position/sigma/Δ/ξ evidence)

ProtectedVarAt(k,v,sigma,u)
SourceUpperUse(u,v,U,sigma)   [original complete Function upper view]
---------------------------------------------------------------- Dir-Protect [selected boundary]
NewProtection(k,u,outEff(U))  [designated covariant/output-effect occurrence]

that SAME seed + retained ProtectedVarAt(k,v,sigma,u),
SourceUpperUse(u,v,U,sigma), NewProtection(k,u,outEff(U))
+ resolved callee use of b_f + ordinary formal x
syntax-directed Value(A_x) entry + actual result-rebind/name evidence
at this scoped call + authentic captured-use chain where present
---------------------------------------------------------------- RefineFormal [C5]
NonHandlerFormal(b_f,F_shared,this-use; original source Δ/ξ)
retain the same seed/upper-use/output-effect protection evidence
```

This is a candidate connective rule for the approved examples, not a generic `Value-entry argument ⇒ Pure` rule. The conclusion is NonHandlerFormal in the shared inferred relationship, not `Act(v,U,r).role=Pure`, and not a change to the supplied callable's stored entry. It refines the provisional state; it does **not** remove protection merely because the Handler seed is discharged. The selected annotation-absence seed protects only `outEff(U)` at this original source upper-use; retain the seed and exposure evidence through refinement. It does not recursively mark nested effect positions.

The selected no-backflow condition is explicit: an existing lower/provider occurrence `'e -> ['g] 'h <: 'f` does not acquire protection on `'g` from the protected inferred `'f` or its upper-use mark. Independently existing provider marks survive. Preserve separate original upper/lower occurrence identities and seed identities even when erased endpoints or printed types coincide; a solved-effect bit cannot replace these records. A known external Name receives no new unannotated-formal seed from Name lookup. This protects an inference view; protection of a concrete event/profile additionally requires its actual source contribution, typed incidence, receipt and live receiver evidence. No ordering, recursive seed aggregation or late-seed replay policy is supplied. The precise lattice/constraint interpretation, multi-use conflict rule and principal completion of these two judgments remain open. C5 deliberately does not equate NonHandler with a concrete Pure callable descriptor.

C6 proposes a local permission record for an actual annotation occurrence:

```text
admitted source annotation a: f: _ -> [io] _ at original position
independent typed annotation/Flow incidence to contribution k at that position
---------------------------------------------------------------- PermitLocal [C6]
MayRemove(a,io,k;original scope/owner/path/ξ)

MayRemove(a,io,k) + original lawful removal/visibility evidence at that incidence
---------------------------------------------------------------- RealizeLocal [candidate obligation C6]
realized boundary target with its local evidence; prior evidence retained
```

`MayRemove` alone has no operational removal conclusion. Unrelated effect contributions and provider-owned protection remain. The actual boundary compares its direct current endpoint with its target and exports that target with its local realization evidence; it cannot skip an intermediate annotation or back-protect a lower/provider occurrence. This note supplies no numeric subtraction/pop count, handler selection or concrete removal algorithm. Without the genuine annotation-to-contribution incidence and lawful realization rule, permission remains unresolved rather than being applied by family-name matching. Annotation/callback overlaps and arbitrary annotation syntax remain outside this candidate rule.

## 5. Decision table, transport and comparison independence

| Source/evidence case | Formation and constraint action | Role/entry/protection consequence | Exact residual |
| --- | --- | --- | --- |
| Unannotated inferred f, ordinary x, exact approved component | FormCall then SeedFormal/RefineFormal on one shared contract | NonHandlerFormal refinement retains `ProtectedVarAt(k,v,sigma,u)`, `SourceUpperUse(u,v,U,sigma)` and `NewProtection(k,u,outEff(U))`; no backflow to lower/provider occurrences; independent provider marks survive | C5's principal interpretation and component conflict resolution |
| Explicit f annotation containing io | Retain annotation slot, direct boundary check and candidate PermitLocal incidence | Only corresponding io permission; removal requires independent evidence | C6 incidence/realization completeness |
| Existing Pure callable at callback slot | Retain actual Act and compare its completed contract | No rewrite to Handler, no new entry/wrapper from checking | Complete joint inclusion certificate |
| Literal at known callback slot | Normative B: expected Handler boundary first; independent parameter/body/result; one F_lit <: F_cb | Literal introduction from context; parameter entry still from syntax | B-equivalence for any early propagation |
| Whole argument tagged Value(A) | Pass Delay of Result=Comp(empty,A); check whole carrier | Actual receiver controls entry; latent A is not recursively forced | Carrier/admission and actual receiver obligations |
| Whole argument tagged Computation(E,A), even E=empty | Pass Delay of Result=Comp(E,A), preserve source tag/designated consumer | Tag/entry does not change from row shape | Complete computation inclusion/typed paths |
| Pure immutable Name callee, selected identity result | Reuse ReadInvoke and IF | Staged same-provider complete result; no early challenge/receipt | Actual value inclusion, whole-carrier check and guards |
| Effectful/computed callee or unrelated result | Retain all child and dependent schemas; emit explicit open obligations | No Name identity-rule extrapolation | C4 general result constructor/checking |
| Independent W/Z whole-Call alternative | Retain actual declaration/IF placement and full arm contract | No source witness demanded; no deleted arm | Original hard envelope/provider/future/domain laws |
| No authentic Gen-Call-0 emission | Retain current call/children and open supplier | No fabricated O0 occurrence or annotation restriction | C2 all-source emission |

C7 proposes preserving the entire generated obligation/frame package through every actual generalization/use transformation by source-contract §3.4's certificate inventory. Whole injective freshening transports bound logical coordinates, F_shared, role-refinement evidence, annotation permissions, every incident K/D/path/owner field and all W/Z/guard/admission interfaces together. C5 transport also retains seed identities and separate original upper/lower occurrences with their `ProtectedVarAt`, `SourceUpperUse` and `NewProtection` records; endpoint equality grants no reverse protection. Original static source positions and β templates remain identifiable under that map; fresh logical binders are not new source positions. Rigid captures stay fixed where required. A shared witness is never hidden/freshened per port. A later compatible event uses its live state rather than restoring maker activity. For this exact local step the proposal keeps captured f monomorphic through local binding; selecting broader local polymorphism remains open.

Option A requires independent endpoint/descriptor/role/entry/origin/scope/authority satisfaction on the existing complete Rel_C at one ξ. Option 2 permits independently licensed production extras lacking source execution. C8 retains an explicit open requirement for their exhaustive grammar and all admission laws; it selects neither W/Z meanings nor the sufficient H_G grammar as the production policy. Source certificates alone cannot prove full production membership/containment.

Admission ranges over **all** independently typed compatible punctured contexts with actual callable and whole carrier inserted directly and correlations retained, including future/unreachable/other-program uses. Initial contexts, typed responses, original raw resumes and future call/force are independent admission cases. A domain-changing whole comparison must establish

```text
D_checked ⊆ D_actual
∀h∈D_checked. P_actual(h;ξ) ⊆ P_checked(h;ξ)
```

including production-only alternatives. Actual provider membership is used only *after* a checked challenge has been independently assembled, to supply actual acceptance and output safety. Q is an obligation over this already formed data; it cannot create a source slot/path/capture, dynamic receipt, license, permission, domain or provider. No concrete-success chain replaces the whole comparison. This ordering avoids defining admission or formation by the conclusion being proved.

## 6. Exact nested derivation and smallest separating reductions

Take exactly `my apply f = { my step x = f x; step }`. The hypotheses are:

1. H_src: the selected sequential source meaning, authentic parameter/application/capture and registration origins, original scopes and one ξ.
2. H_core: reviewed Draft §6 source synthesis relative to those lexical interfaces; H_admin only if same-context eliminate(reify) pairs are contracted without crossing a delimiter.
3. H_inputs: independent original complete I_f/I_x and F_c; hereditary actual f from completed outer carrier Return; same-value VIncl(A_f,F_c); whole-carrier checking; fixed independent histories/world/guard/action kernel; every retained original alternative's genuine full contract. These are the selected closure theorem's exact inputs, not supplied by this proposal.
4. H_selected: selected IF, contextual membership, ReadInvoke and captured-closure constructors with their full independent interpretations.
5. H_candidate, only to call this a completed *production inference* package: C1–C8's unselected elaboration/refinement/transport rules have independently sound principal presentations. This hypothesis is not established here, and the symbolic/selected-constructor derivation below does not need it to be asserted true.

Resolve `f` to the outer formal, `x` to the local formal, and final `step` to the local sequential binding. Let P_f=Value(A_f), P_x=Value(A_x). After their respective actual entry rebinds, the Name interfaces retain those Value tags.

```text
f : (Value(A_f), name f, result(name f))
x : (Value(A_x), name x, result(name x))
J_x_lookup = Comp(empty,A_x)
c=f x : (Computation(E_c,A_c), reify(call(n_f,n_x)),
         eliminate_p_c(reify(call(n_f,n_x))))
S_skeleton = Fun(P_x,Comp(E_c,A_c))
step initializer : (Value(S_skeleton), lambda(P_x,n_c), result(lambda(P_x,n_c)))
final step : (Value(S_skeleton), name step, result(name step))
block : (Computation(E_b,S_skeleton), reify(bind(step,n_rhs,n_final)),
         eliminate_p_b(reify(bind(step,n_rhs,n_final))))
apply skeleton : Value(Fun(P_f,Comp(E_b,S_skeleton)))
```

H_src/H_core derive the uncontracted term and, under H_admin, precisely

```text
lambda(P_f,
  bind(step,
    result(lambda(P_x,
      call(result(name f),result(name x)))),
    result(name step)))
```

E_c,A_c,E_b remain symbolic complete relations' endpoints. The pure x lookup follows *after* step's incoming I_x carrier execution; I_x may expose effects, pending requests or divergence. It is not identified with J_x_lookup. FormCall/IF retains the original captured f root and checking F_c, Delay(n_x), actual provider schema and all arms. The candidate refinement records NonHandlerFormal on that same capture/formal contract, without changing the eventual actual f.

Under H_inputs/H_selected, the exact selected semantic refinement is

```text
R_c = ReadInvoke(F_c,D_c,IF_c)
F_step = Strict(I_x,x:A_x,R_c,IF_step)
R_local = original ordered Bind image of
          PureReturn(F_step) and final PureReturn(F_step)
```

Raw Lambda/Name/Result/Delay/Bind/Call constructors first give finite M_E witnesses. Descriptor membership is not used to manufacture them. The selected Step theorem then constructs actual captured step membership and installed world simultaneously; Block types the same inert RHS, ordered binding and final returned closure. OuterTrace appends `rebind-f; construct-step; rebind-step; return-step; invocation-return` to a pending outer raw handle, returning that exact captured step on completion. Later step calls use the then-live context and same captured f. No terminal step Call occurs in the block.

This is a conditional composition of already selected results. It leaves H_inputs as genuine obligations and proves neither an arbitrary independent F_apply nor the printed skeleton's equality with a complete descriptor. A full outer interface must match the displayed complete entry/return composition or have its genuine whole comparison. It is therefore incorrect to repeat the historical claim that complete IF placement or exact step introduction itself remains unconstructed.

Two smallest symbolic separating reductions discriminate forbidden shortcuts (no executable experiment or new source decision):

* `id x=x`, Value entry, with an admitted carrier `Request(E,k)` then Return(Int), no eligible ambient handler. Pure body lookup returns Int, but complete invocation exposes E at entry. This refutes J_call=J_body and the empty argument-effect shortcut.
* Constant Unit body with retained computation entry and the same admitted carrier does not force it. Complete invocation need not expose E. This refutes an unconditional exact `incoming-support ∪ body-support` result rule. The carrier may instead diverge with empty support, still distinguishing Value and retained entry.

Each witness is conditional on the existing typed-core/selected entry rules and compatible independent context. They are reductions, not Oracle observations or proofs that the proposed constraint generator implements those rules.

## 7. Unselected choices, alternatives and failure conditions

| Candidate choice | Alternative and consequence; exact blocker |
| --- | --- |
| C1: one retained FormCall package, syntax-directed child construction before comparison | Reconstruct later from IDs/query results: requires inverse/incidence proofs and cannot manufacture missing source evidence. The selected IF cases support retention, but a production API/elaboration contract is unselected. |
| C2: authentic Gen-Call-0 emission remains a distinct supplier, not synthesized from a generic Apply record | A uniform all-source generator may eventually supply it; extending the adopted definitions alone does not. No all-source generation theorem is supplied here. |
| C3: symbolic whole-argument/callee/complete-result obligations retained as active correlated relations | A finite structural subtype presentation may discharge them; bottom/empty four-port projection cannot. Effective solving, reflection and principal completion are open. |
| C4: selected Name/identity result reuse; computed/unrelated cases explicitly open | A generalized result constructor must cover callee effects, staged actual provider and full independent result checks. ReadInvoke's selected scope does not entail it. |
| C5: candidate shared Seed/NonHandler refinement limited to approved patterns, incorporating the selected directional boundary | An equivalent declarative joint constraint interpretation may avoid temporal mutable state; it must retain `ProtectedVarAt(k,v,sigma,u)`, `SourceUpperUse(u,v,U,sigma)` and `NewProtection(k,u,outEff(U))`, separate upper/lower occurrence and seed identity, no backflow to an existing lower/provider occurrence, independently present provider marks, and all principal solutions. Directional protection is already selected, not an open alternative. Generic Value⇒Pure, rewriting actual f, recursive nested marking or blanket event protection is forbidden; event-to-profile claims require actual contribution, typed incidence, receipt and live receiver evidence. The lattice/constraint interpretation, conflict/recursion/multiple-use rules and principal completion remain unresolved; no ordering or recursive aggregation policy is selected. |
| C6: explicit annotation-local permission/incidence plus separate lawful realization | An equivalent integrated profile judgment may suffice; global row subtraction or same-family matching does not preserve approved scope. Release at the realized annotation slot versus release only with a live eligible handling opportunity are distinct candidate activation conditions, supplied by the primary's bounded falsification lane; neither is selected here or certified as a complete model. The concrete incidence/removal derivation is missing. |
| C7: transport full package by certified whole maps; no fresh local polymorphism assumed for this step | Broader local generalization needs its own capture/role/permission/admission preservation and principal rule; the nested addendum selects none. Exact generalizer/use correspondence remains open. |
| C8: exhaustive production grammar/admission obligations remain open | A separately reviewed original full grammar or a certified paired abstraction may close them. Imposing source-tight membership contradicts Option 2; selecting H_G or W/Z now would exceed this proposal. |

The precise blocker is no longer static contextual placement or the scoped constructed closure. It is the unselected production source constraint/refinement/transport presentation and realization of the selected directional protection boundary plus complete independent kernel/arm laws at the intended production endpoints. A checker implementing the same proposed relations would leave these premises untouched; a further equivalent toy probe is not the next method. Review the concrete candidate choices against the accepted contract and then construct a discriminating source/production bridge once they are selected.

Failure conditions include changed dependent bytes; absent authentic formation origins; independently recombined ξ/witnesses; actual provider/entry rewritten by the checking view; challenge made contingent on Q/actual safety; carrier required to return; dropped pending/future cases; lost annotation incidence or prior evidence; upper/lower occurrence or seed identity erased; upper protection back-propagated to a provider; event protection asserted without contribution/incidence/receipt/live-receiver evidence; restored exited maker authority; unlicensed/omitted Option 2 arm; incompatible whole transport; unmatched outer/result descriptor. A failed conditional certificate blocks the claimed result, not the source program by a newly invented rejection policy.

## 8. Verification, dependencies, resources and review boundary

Checks: read-only branch/HEAD/status; governing policy/section reads; integrated approved-answer byte equality at pinned HEAD; SHA-256 direct-input checks before writing; creation guard; artifact readback, scope and hash checks at handoff. Initial aggregate reads were truncated; decisive governing sections were reread in narrow complete captures. A lookup of a nonexistent theory companion to the pure-read definition failed; no result relies on that absent path. No exhaustive repository search is claimed.

No executable oracle, tests, builds, compiler/Oracle runs, mutation probes, performance samples or random seeds were used. Executable ranges/seeds/mutation count are not applicable/zero. The derivation shares the selected source/typed-core/constructor assumptions; it cannot independently validate them. The two reductions attack named shortcuts under those assumptions. Independent reviews of reused results are their provenance, not certification of this note. The initial frozen proposal subsequently received batched spec-auditor/compiler-referee review; this repair applies the accepted directional-protection omission. The repaired delta awaits independent review; producer readback does not certify it.

Budget: one Markdown artifact, zero tests/builds, lightweight static reads only. Maximum concurrent lightweight read processes: four in the initial batch; no heavyweight processes. No numeric CPU/RAM/wall limit was supplied; aggregate CPU, peak RSS and full wall time are uninstrumented. Reads completed within individual tool calls. No shared outputs, compiler edits, formatter effects, Git mutation, subdelegation, interactive questions or question-board writes.

Unverified: production parsing/acceptance/execution; effective constraint generation/solving/principality; generalization/use implementation; C5/C6 rules; complete production grammar/admission/Option 2 conformance; arbitrary computed/effectful callees, unrelated result descriptors, State, adapters/imports, recursion and broader local polymorphism. No DAG or gate status changes follow. Repair verification: exact pre-repair artifact SHA-256 `05bfebe5f363b2616c964964034134c019cf5bd774650a37c10bfab751c74204`, branch/HEAD/status, directional addendum §§2–4 and current hash, exact leased-path textual diff and post-repair hash. Repair used only lightweight reads and one Markdown edit, with zero tests/builds/probes; CPU/RSS/full wall time remain uninstrumented.

| Direct dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-07-original-call-formation-definition.md` | `4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/theory/2026-10-08-apply-step-core-skeleton-ledger.md` | `796e0f4993997769fa8610a1c377731d999f5629368aaa1fdba597a3663ae4f1` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-solver/src/lib.rs` | `236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2` |
| `crates/yu-solver/src/shadow_apply.rs` | `2b59eb0b327df89a5fbfb5373de9f01f73c0aaeca06b406c289e4aa7f5116dc3` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/design/2026-10-08-pure-read-call-result-constructor.md` | `8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |

Recommended next action: primary should obtain focused independent delta review of this directional-boundary repair, then adjudicate C1–C8, resolve which missing judgments can be formalized under the current definition authorization, and present any genuine unresolved semantic alternatives for user adoption before a production design/implementation. User adoption of this research note is not implied by existing approvals; no rerequest is needed for the already selected directional protection or IF/Step/ReadInvoke scopes.

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-08-production-call-elaboration-proposal.md` only.
- Baseline SHA: `4288e155e76f23c74263cf3e0023463a3f393b3b`; branch `research/simple-sub-intrusion`.
- Changed dependency hashes: none of the original pins at prewrite check. Added dependencies are the newer IF/closure definitions/proofs, semantic input proof, pure-read result definition and callback delivery, with exact hashes above. This repair additionally pins the directional protection addendum at `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7`; its bytes were unchanged. Dirty code pins are descriptive boundaries, not source authority.
- Claim/review status: frozen Draft, non-authoritative candidate contract; initial batched review finding repaired, repaired delta awaiting independent review; conditional nested composition and reductions; no new theorem/production/DAG closure.
- Checks already run: policy/governing reads, exact approved-answer equality, SHA-256 pin checks, creation guard, leased artifact readback/scope/hash. Repair adds exact pre-repair artifact/directional-dependency hashes and leased-path diff/post-repair hash checks. Zero tests/builds/probes.
- Proposed one-line checkpoint commit message: `research: retain selected directional protection in Call elaboration proposal`.
- Shared-record deltas intentionally left to primary/curator: link this candidate; record remaining C1–C8 obligations, with C5 directional protection already selected and its connective/principal rules still open; refine the older ledger's supplier boundary with selected IF and Step results; keep all aggregate/DAG/production statuses unchanged. No shared task/index/authority/question-board/manifest/lockfile edits requested as part of this checkpoint.
