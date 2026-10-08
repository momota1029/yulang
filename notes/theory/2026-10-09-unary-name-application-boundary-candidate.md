# Unary Name application: source ownership and consumer boundary

Date: 2026-10-09
Status: Draft; non-authoritative research; independently reviewed within this scope
Review: `compiler_referee` and `spec_auditor`; no findings at SHA-256 `d119b318a1ea990a8ed9f71530db52b014c56a5c858d5072f4a3185de9a192cf`
Method: bounded source/code correspondence and conditional structural derivation
Baseline: `1c252c7731ae8c3772740a56bbc30ed8447cfa75`
Exclusive lease: this file only
Production implementation, supported successor case, F5 replacement and gate closure: none

## 1. Objective, corrected witness and scope

Identify the earliest missing source-owned evidence for the intended ordinary
unary call, and distinguish its construction from semantic admission and
solver consumption. The assignment's spelling was
`my id x = x; my use y = id y`. That spelling is unsuitable: the parser selects
prefixed `UseDeclaration` for `my use y ...` before the binding parser. See
`crates/yu-syntax/src/declaration/use_decl.rs:217–264` and
`crates/yu-syntax/src/declaration/binding.rs:33–52`. This is a parser obstruction,
not evidence against the intended ordinary call semantics.

Use this corrected candidate shape for the crosswalk:

```yu
my id x = x
my wrap y = id y
```

The two lines avoid assuming same-line separator acceptance. No parse, HIR or
solver execution of this exact source ran. Existing paired fixtures that
permit paired errors cannot establish its success. All formation statements
below require the recovery-free resolved source shape specified in H1.

The envelope has two immutable unary declarations, two unannotated value
parameters, one parameter Name body and one application of a module-definition
Name to a local-parameter Name. It has no integer operand, higher-order formal
callee, annotation, conversion, handler, State, import or recursive SCC.
The missing literal Result owner is outside this envelope. Neither x nor y
being callable data would change their outer Value parameter tags; latent
values are not recursively forced. No provisional higher-order formal-role
inference is used.

This is a bounded characterization of construction responsibilities. It is
not a minimal-counterexample search or a theorem that all Name/Name calls are
admitted. The conditional derivation in §4 does not assert its missing premises.

## 2. Exact authority and decisions already settled

The operating rules read in full were research-lab, design-authority,
git-concurrency, workflow and orchestration-budget. The task locator is
`tasks/current.md:2986–3038`, read as navigation, not semantic authority.
Artifact production uses M0 record-only process: one producer, zero reviewer
claims, static checks only; any independent review is primary-owned.
Convergence means one complete bounded field map, explicit missing judgments
and a falsifiable next evidence request, with no compiler change.

The governing source scopes are:

| Source | Settled contract and retained boundary |
| --- | --- |
| [Source Call interfaces](../design/2026-10-08-call-source-interface-definition.md) §§2–4; [IF construction](2026-10-08-call-source-interface-construction.md) §§3.2,5 | IF-Insert/IF-Use and Name/Result/Delay/entry/Call constructors retain whole contextual interfaces, declaration/reference placement, actual provider and dependent return/future slots. Original operator typing, admission, phase/dispatch, hole/world and lawful actions remain inputs. Placement is not membership. |
| [DemandFormation cut](2026-10-08-call-demand-formation-construction.md) §§2–5 | Conditional receiver elimination consumes complete independently checked inlet admission. §5 identifies the unsupplied pre-comparison whole-argument-to-inlet transport and declared entry/role incidence; it does not establish them. |
| [Source Generalize](../design/2026-10-08-source-generalize-definition.md) §§2–4 | Final source root, publication-indexed provenance, fixed anchors, eligible ordinary Desc declarations, independent frames versus aliases, and one residual joint relation are selected. Genuine local constructor laws and production discovery remain required. No new instance of a missing Name/Name Call law follows. |
| [Result choice](../design/2026-10-02-source-result-synthesis-choice.md) §§1–2; [schedule choice](../design/2026-10-02-source-call-scheduling-choice.md) §§1–2 | Callee first; Delay stores the whole argument inertly. Unannotated x/y own Value entry with one Force and typed rebind in the actual receiver, before body. Result forwards the original source tag. These are approved choices. |
| [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md) §§6,9; [initial source construction](../progress/2026-10-06-initial-context-source-construction.md) §4.4 | Relative Name/Lambda/Application `(I,d,n)` skeleton and ReceiveSchema; complete invocation depends on the received carrier and actual producer. This reviewed Draft/conditional machinery does not establish raw-source solving or a complete call scheme. |
| [Source Call generation](../progress/2026-10-06-source-call-generation-construction.md) §5 | `WF_Dec`, `VIncl`, whole-argument checking, complete-result `CIncl`, and decorated `TypedCallCert_Dec` retain distinct obligations. The decorated certificate is supplied, beyond generated incidence. |
| [Inferred Function views](../design/2026-10-05-inferred-function-call-views.md) §§2–3,5 | Source identities, typed paths and joint `xi=(nu,K,D)` precede Q. Complete admission is independent. §3's higher-order formal inference is not a generic Value-entry-implies-Pure rule and is not this witness. |
| [F5 foundation](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md) §§1,4,29–30 | Current identity Lambda/parameter source ownership, monomorphic local references, module use routing and one live bound authority are approved. §1 expressly excludes expression application typing. |
| Integrated `flat-application-owner-family` q1/d1, option 1; [selected proposal](2026-10-08-flat-application-owner-completion-decision-object.md) §§3–6,9 | Selection covers direct resolved formal Name/Int literal only. Its §9 typed-child composition is a future seam, not adoption of module-root Name/local-parameter Name. Receive-N is not TypedCallCert_Dec. |

Only committed q1/d1 receipt and approved-answer bytes from the pinned revision
were consumed. No pending question-board contents were read. The literal-case
selection must not be silently extended to this corrected witness.

## 3. Field-to-owner/consumer crosswalk

Names such as c, u_f, u_a, o_arg and p_out below are explanatory labels for
distinct occurrences/roles, not allocated compiler IDs or selected new
judgments. Native complete-interface fields cannot be reconstructed merely
from an existing `HirOccurrenceId` or solved endpoint.

| Field/input → required output | Source-owning construction and semantic consumer | Actual retained HIR/solver evidence; missing evidence |
| --- | --- | --- |
| Parsed declaration/parameter/operand nodes and ranges → admitted shape | Parser owns binding Pattern topology and ML argument association; source lowering owns admission. | `lower_module`, `plain_binding_header`, `lower_body`, `lower_simple_chain` in `yu-hir/src/module.rs`. x/id are in the existing unary envelope. c's non-leaf associated expression is rejected by ordinary `lower_simple_chain` before child lowering. Corrected exact source acceptance is not executed. |
| id/wrap declaration identity, x/y binder ordinal and artifact → roots and parameter bindings | Declaration registration and scope entry; Name lookup and later source Generalize consume original roots. | `HirBinding` retains root, parameters, Lambda/body ownership. `HirParameterId` retains owner+ordinal. This is nominal/lexical identity, not a complete source Desc interface or semantic world anchor. |
| u_f's actual Name occurrence and local-first resolution → module id use at c | Name formation/IF-Use follows the actual definition reference and scoped instance. Callee normalization and callee checking consume it. | `lower_leaf` gives `NameResolution::Resolved(DefId)` only when reached. Shadow Apply lowers the Name and records its source key; ordinary rejected c has no separately resolved operand. Module-use instantiation and source-native whole contract at this nested use remain unsupplied. |
| u_a's actual Name occurrence and resolution → y's monomorphic operand | Parameter Name formation reads y after wrap entry rebind. Argument Result/Delay consume its original Value interface. | `NameResolution::Parameter(HirParameterId)` is the existing resolution category; shadow can retain it. Existing parameter Name Lambda body has effect facts and reuses the parameter value row. That recipe is not a nested argument typed-owner certificate. |
| Parent c, separate callee/argument children, enclosing Lambda/root → containment/incidences | Source constructor creates actual parent/operand inclusions and containing scope. IF consumes these, with IF-Insert/IF-Use for declarations/references. | `ResolvedExpr::Apply` has occurrence, source_form, callee, argument, errors, range. Ordinary lowering emits Lambda(Error); shadow emits structural Apply with UnsupportedExpression. IDs do not encode the parent by themselves. No ordinary typed Call owner is retained. |
| Operand interfaces `I_f,I_a`, data `d_f,d_a` → distinct Result ports/code `n_f,n_a` | Name law plus original-tag Normalize creates Return of Value data, preserving provider/current configuration and latent future reference. | The mathematical Name/Result case exists relative to original laws. Existing collector has leaf/Lambda rows and recipes, not these native ports. Name-only avoids Literal-N but does not prove original Return-image realization for the actual nested source operand. |
| Entire `n_a` and lexical captures → inert `Delay(n_a)` and open whole-carrier inlet | Source Apply/Delay construction owns argument origin; actual receiving Function consumes the whole carrier. | Shadow child pointers identify syntax; no production Delay/carrier/inlet field. Must retain whole original interface, current world, provider/future/pending fields and the open hole, not just y's value endpoint or source diagonal carrier. |
| id's actual callable declaration/body → generated Value entry and complete producer interface | id owns receipt, designated Force, typed rebind of x, body and invocation return; wrap separately owns analogous entry for y. ReceiveSchema refers dependently to the actual later producer. | `LambdaRecipe` carries parameter position, root/body/effect components and fact order. `admit_lambda_fact` creates current positive Function. It has no native receipt/entry/role/profile/complete-call certificate. No new role label is inferred from Value entry. |
| Complete selected `F_c`, declared inlet, shared source contract → symbolic demand and independently checked admission | Owning source declaration/use must form inlet/entry/role incidence before Q. Descriptor kernel establishes `WF_Dec`, same-value `VIncl`, whole-carrier compatibility and contextual guards. | No ordinary collection field for F_c, its inlet or native checked challenge. §5 DemandFormation's transport remains candidate/unsupplied; actual-U acceptance cannot supply this earlier admission. |
| ExecuteCallable image and complete output → `Comp(E_c,A_c)` result, Reify and designated one-layer consumer | Call owns complete result, separate inert data/reified result and known consumer origin. id body Result differs from its complete invocation. wrap forwards c's Computation tag. | Ordinary Error body creates no Call result/body component or Lambda recipe. Native result `CIncl` is unsupplied. Do not set E_c to empty merely from id's pure body, nor identify the call result with y or id's body row. |
| Lexical u_f, separate checking u_c, argument check and result check → original check origins/consumer attachment | Source check construction and exact indexed pairing; decorated consumer requires full `TypedCallCert_Dec` plus same-operation/scope/tuple pairing. | Current `ConstraintOccurrenceId(occurrence,slot)` and `CauseId` preserve admitted fact causes, not native profile/operation/correspondence fields. Structural ReceiveSchema alone does not produce the decorated certificate. The q1/d1 checks belong to the selected literal case. |
| Value versus Computation tags, introduction/consumer origins, annotation absence and latent providers → typed provenance | Each owning constructor, then source Generalize dependency closure and lawful use. | HIR variant/`source_form`, ranges and optional source keys are structural provenance. `EvaluationClass::FetchValue` classifies Lambda construction. None supplies source-native publication-indexed Desc/EventProof scopes or permits a solved-shape-driven force. |
| One joint `xi=(nu,K,D)`, scoped substitutions and dependent CalRet/Bind/return fields → coherent assignment and complete incidence | Complete source component formation and original laws, before challenge/history; admission and Generalize preserve the same joint tuple. | Current private component/live-variable maps, term lineage, branded roots and routed use provenance belong to F5. Equality of row indices or independently successful queries is not a native joint-assignment bridge. No map into these fields is established here. |
| Ordinary components/facts/uses → SCC solving, generalized scheme and atomic result | Current `ConstraintBatch`, `InferenceSession` and `SolvedModule`; future production consumer must retain authentic source evidence through solve/use/publication. | `collect(hir)` calls `collect_mode(hir,false)`; Lambda(Error/Apply) is Error and `emit_lambda` falls through. Pending shadow rows explicitly remain ApplicationTypingRuleUnresolved. run admits facts, executes SCC plan and finishes; unsupported roots can have rows without a Function recipe. Native acceptance/lifecycle correspondence is absent. |

## 4. Conditional derivation and exact hypotheses

Fix a single recovery-free finite source artifact and actual scopes, not just
the displayed strings. The conditional derivation requires:

- **H1 (shape/ownership):** the corrected two-binding source resolves to the
  stated unary declaration graph; u_f selects id and u_a selects wrap's y,
  with the real containing Lambda/c incidences and no recovery.
- **H2 (ordinary child laws):** original typed Name, Value Result/Return,
  Lambda entry, typed rebind and world/latent-provider laws apply at those
  occurrences, jointly under one scoped xi. id's module-root instance and y's
  monomorphic binding are supplied by actual source rules.
- **H3 (Call owner supplier, absent):** a typed ordinary Name/Name Application
  rule constructs the complete demand, original inlet/entry/role incidence,
  output/check/Reify/consumer origins and source-interface attachment. H3 is
  neither selected Application_N membership nor an existing HIR Apply field.
- **H4 (admission and checking, absent):** independent interpreted WF_Dec,
  VIncl, whole-argument-to-declared-inlet transport with contextual guards,
  full decorated certificate/pairing and complete-result CIncl hold at the
  same assignment/provider/current configuration. No Q success creates them.

From H1–H2 and typed-core §6, assign `P_x=Value(A_x)` and
`P_y=Value(A_y)` before body synthesis. id's body Name reads x at Value(A_x),
so its body Result skeleton is `Comp(empty,A_x)` and its Lambda data skeleton
is `Value(Fun(P_x,Comp(empty,A_x)))`. This is a body/result skeleton relative
to H2; it is not id's solved complete-invocation scheme.

At c, Name id obtains its actual source instance `I_f=Value(A_f)` and Name y
has `I_a=Value(A_y)`. Normalize by those source tags to `n_f=result(d_f)` and
`n_a=result(d_a)`. c stores all of n_a inertly as Delay after callee evaluation.
H3 then supplies the occurrence-owned Call assembly and actual producer's
dependent receipt/entry/body/result-consumer suffix. H4 is precisely what
makes this structural assembly a typed admitted call with complete output
`I_c=Computation(E_c,A_c)`, `d_c=reify(call(n_f,n_a))` and its designated
`n_c=eliminate_p(d_c)`. wrap's result forwards `Comp(E_c,A_c)` by the original
Computation tag. E_c/A_c are constrained names, not solved outputs.

Each inference above preserves H1's occurrences and H2–H4's one joint tuple.
IF-Insert/IF-Use place independently formed contracts but cannot manufacture
H4. Source Generalize can subsequently close eligible ordinary descriptions
relative to genuine local laws; it cannot supply H3/H4 by generalization.
Current F5 consumption cannot supply them by live-row allocation either.

Thus the conditional conclusion is a relative source skeleton and a list of
exact required semantic premises. The established code conclusion is narrower:
ordinary lowering rejects the non-leaf c before operand resolution, and the
ordinary collector cannot consume this Call. No admitted-program
counterexample, new source rule, principal scheme or cutover follows.

The actual callable's role is still an independently supplied/generated
producer fact; Value entry alone does not provide it. In the original consumer
vocabulary the full typed instance also needs genuine `M_E`, selected
`ReadInvoke` formation, the typed owner interpretation into IF, and full
`CallMem`/`C0` with their matching original indices. The already selected IF
placement constructors are not reopened: the unsupplied evidence is this
Name/Name owner and its authentic typed input/consumer pairing. None of these
inputs follows from shadow structural parity or its paired-error fixture.

## 5. Falsifiers, independence and next minimum evidence

Stop this proposed route if any of the following occurs:

1. The exact corrected source is not two recovery-free unary bindings or its
   actual operand resolution differs from H1. Repair the witness before using
   any semantic derivation; never change parser expectations to fit it.
2. A supplier labels this module-root Name/parameter Name pair as already
   selected q1/d1 Application_N. The approved domain is different.
3. The same source Call lacks a complete typed inlet/entry/role incidence, or
   its transport requires Q success, independent port witnesses, a substituted
   provider/world, matching printed endpoints or actual-U acceptance.
4. ReceiveSchema is equated with the decorated certificate, or a complete
   Call image is replaced by its closure body row/argument endpoint.
5. A solver map drops source tags, whole-carrier fields, original checks,
   scopes/provider dependencies or unexecuted independently declared arms,
   or publishes partial results after construction/solve failure.

These are falsifiable dependency checks, not executed mutations. No seeds,
integer ranges or random enumeration exist; coverage is one conditional
structural candidate, two parser selectors and the named HIR/collector/session
entrypoints. No independent oracle ran. Source law premises and code facts
are separate evidence kinds; the source documents and compiler can share
assumptions. A future checker hard-coding H2–H4 would test consistency of that
model, not establish those source rules. Independent review has not occurred.

The prior DemandFormation record already tried argument-result matching and
Strict/operational inversion without supplying the same inlet-admission
premise. This note performs neither attack again. Its different method locates
the construction owner and shows the earlier domain mismatch and ordinary
HIR refusal. A third endpoint probe would not reduce that premise.

**Recommended next action (future proposal gate, no implementation authority):**
prepare a reviewed bounded Name/Name source-owner proposal for the corrected
resolved shape. Its minimum evidence must construct the module-root instance
and local-parameter child ownership, whole argument Result/Delay and exact
inlet/entry/role transport, then pair the independent decorated certificate
at the same Call. Validate H1 narrowly before semantic use. Return adoption
and implementation questions to the primary; no compiler edit is authorized
by this artifact.

Unverified scope: corrected exact parse/HIR execution, same-line separators,
ordinary typed Name/Name owner/bridge, whole-inlet admission, complete decorated
typing, M_E/ReadInvoke/IF applicability/CallMem/C0, all-source validity,
foreign kernels/arms, CallInitial/I0/SeedExposure,
actual protection/profile inventory, State/recursion, solver/generalizer/export
correspondence, completeness/principality, Oracle compatibility and production
cutover. Excluding these here changes no supported source contract.

## 6. Checks, dependencies, resources and commit packet

Checks performed: bounded `sed` and `rg` source/section reads; exclusive-path
nonexistence check; SHA-256 and byte equality between 21 read dependencies and
the pinned baseline; committed q1/d1-only loading. All 21 comparisons matched.
The two parser files were subsequently inspected at the primary's supplied
locators; their individual baseline byte equality was not checked. No
tests/builds, checker, formatting, Git mutation or child delegation ran.

Process deviation: despite the packet's literal “No ... Git” restriction,
the producer used read-only `git rev-parse HEAD`, `git status --short`,
`git ls-tree -r --name-only 1c252c773 questions`, and `git show 1c252c773:<path>`
for baseline verification and committed dependency loading. No index/ref/worktree
mutation occurred; the primary was notified and no further Git commands ran.

Resource envelope: lightweight shell reads plus one artifact write and static
artifact checks; zero build/test/search-probe processes. Batched read subprocesses
were lightweight, not compute probes. Exact CPU, peak RSS and total wall time
were not measured; no numerical resource bound or exhaustive repository search
is claimed. The no-build/no-test budget was preserved.

Critical dependency SHA-256 snapshot (all matched baseline except pinned-only
question bytes, which were never loaded from the live question directory):

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/theory/2026-10-08-call-source-interface-construction.md` | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` |
| `notes/theory/2026-10-08-call-demand-formation-construction.md` | `21310f0a753779a8a8dcac415708ca12ea0e969705a0381a02af97444d4b85ac` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md` | `781d719ef6ddd458908b61b7b95f49e4c6abec9ffed79595af5fe1e201caac83` |
| `notes/theory/2026-10-08-flat-application-owner-completion-decision-object.md` | `61d5fd8e3a359c9ad7fce203ee7927553964b4eeae4a923319aca49a846f826a` |
| committed q1/d1 `approved-answer.md` | `ab2ffb1cd14b023d7159f98f05df480d30772091a77b4079750932e76cab17e2` |
| committed q1/d1 `receipt.md` | `225782741e962b9993e489b26fab41ae2735c16b800afcd967897515922d7a91` |
| `notes/progress/2026-10-06-initial-context-source-construction.md` | `10e86ed3bac72d91f03c83acf50ed8e8336ab3c3d0df4a90a03cbe4efdc7ef75` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `crates/yu-hir/src/module.rs` | `3bb488f9d9e13b43e79e472a65a35197ae4f2c76ae21a6f0f8f77195661f4363` |
| `crates/yu-solver/src/lib.rs` | `236f4f433ef775df0d88294f046e11dd34c1816da2fa99d7f0d403b39c2ed4a2` |

Commit packet:

- Exact leased/changed path:
  `notes/theory/2026-10-09-unary-name-application-boundary-candidate.md`.
- Baseline: `1c252c7731ae8c3772740a56bbc30ed8447cfa75`.
- Dependency hashes changed by this worker: none. Primary must recheck live
  dependency changes before integration; parser-locator equality remains unverified.
- Claim/review status: Draft bounded correspondence and conditional skeleton;
  independent review pending, no selected Name/Name case or gate closure.
- Checks already run: narrow reads/searches, dependency comparison/hashes,
  lease nonexistence and static artifact checks reported at handoff; no tests/builds.
- Proposed one-line research-checkpoint message:
  `research: map unary Name call ownership and admission boundary`.
- Shared-record deltas intentionally left to primary/curator: link this bounded
  draft from the current ordinary Apply audit; record the corrected wrap witness,
  the q1/d1 domain mismatch and H3/H4 supplier boundary. Do not change DAG status,
  authoritativeness, approved scope or implementation permission. No shared file
  was edited.

Writes stop at handoff before frozen review. Any repair requires a renewed lease.
