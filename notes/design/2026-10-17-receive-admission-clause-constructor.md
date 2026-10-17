# Original F2 admission-clause constructor — candidate source rule

Date: 2026-10-17  
Status: Draft / unselected source-constructor proposal  
Sprint: receive-admission-clause-construction-20261017, contract rev1  
Parent: original FORWARD-FIRST-CALL A/B remains OPEN  
Semantic adoption: none; compiler authority: none

## 1. Result sought and exact source

The target is the original receive source and its original coordinates:

receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)

c1 = f(Unit)
c2 = g(Unit)
a2 = c2's original Unit argument
F2 at (sigma2,Delta2)
xi = (nu,K,D)
B_in = incoming computation view at F2's original ports

The reviewed comparison and bridge leave two questions open at this exact F2: checked-inlet admission must eliminate to the full incoming-view relation (VIEW), and full incoming-view evidence plus every original pre-entry clause must introduce the same admission (CHECK). This document proposes the missing source producer instead of assuming either direction. It does not choose I2=SAT, B_in=J_U, or a provider during formation.

The source owner is the resolved declaration/definition/use component that forms the original Function view at the Name-to-Call incidence of g(Unit). F2 allocation alone does not form its interpretation. The actual candidate implementation owners are crates/yu-solver/src/candidate_source.rs, candidate_call.rs, candidate_scheme.rs and shadow_apply.rs; their current retained native incidences do not themselves assert this semantic constructor.

## 2. Dependent input telescope and occurrences

Let Src2 be the finite registered source/descriptor graph rooted at the original F2 occurrence. Do not replace it with all syntactically reachable or all satisfying clauses. Its producer records:

- d_f and original A1 at the declaration/definition occurrence;
- the original F2 root and (sigma2,Delta2,xi) at the resolved c2 use;
- the source occurrences of declaration clauses q and their original dependent interface IF(q);
- the actual scoped substitution m from each q to each use;
- the full argument/carrier reference at c2, actual source child a2 and registered hole/root identities;
- dependent event coordinates e=(eta0,h), live C_e/w_e, and the later actual provider/result coordinate only below an actual Return;
- original operand identities, K/D atoms, licenses, captures, profile/role/entry, paths and event references.

For a declaration occurrence q, retain its own complete ordered telescope

T_q = (indices; operands; evidence; providers/worlds; event; result/future fields),

with each later field dependent on earlier fields in its original scope. It is invalid to project a row/effect endpoint and reconstruct the rest from a marginal. For an actual use u, IF-Use applies only its source-authenticated substitution m to the whole IF(q), preserving the same witness and clause identity. No source execution or successful membership query may create an occurrence that was not inserted and used.

## 3. Candidate producer judgment

Proposed meta-judgment:

  SourceAdmitProducer(Gamma; d_f,A1,c2,F2,sigma2,Delta2,xi)
      => (Src2, Clause2, A2, C2, P2, Inc2)

Here Src2 is the registered original graph; Clause2 is a finite or registered family of actual original predicates with their entire T_q; A2 is the pre-carrier admission family; C2 is the carrier-observation family; P2 is the invocation-output/future family; Inc2 contains only source-derived IF-Insert/IF-Use maps and original operand actions. These are outputs to construct, not premises. WF_Dec(F2), the complete desired inlet, all-guard validity, VIncl, WholeArgCompatible and CIncl are not inputs.

### S-Insert: original declaration insertion

Given an actual independently typed declaration q with its original predicate R_q over T_q, place the whole declaration and its license/provider/evidence fields at the declared root:

  Decl_q(T_q) ; TypedOriginal(q,T_q,R_q)
  -------------------------------------- S-Insert(q)
  RootSlot(q,IF(q)) ; IF-Insert(q): IF(q) -> RootSlot(q)

This retains exactly the original typed relation R_q. It does not grant its license at another event, prove R_q true, or classify R_q as admission merely because it is stored.

### S-Use: actual source use

Given an actual resolved reference u to q, with source typing supplying its scoped substitution m and containing source/operator frame F:

  ResolveUse(u,q,m) ; TypedUse(u,m,F)
  ------------------------------------ S-Use(u,q)
  UseSlot(u,IF(q)[m]) ; IF-Use(u): IF(q)[m] -> UseSlot(u,F)

For c2, only actual clause roots on the resolved declaration/definition/use path are inserted and only actual typed references in that component are used. A registered but unreferenced foreign root is not silently attached. A root used at c2 keeps its declaration identity and complete substituted telescope.

### S-F2: candidate admission assembly

  Root2(F2,Src2) ; all actual S-Insert/S-Use paths to c2
  ; Clause2 = the original clauses at those paths, partitioned by owning event
  -------------------------------------------------------- S-F2
  CandidateI2 = conjunction of A-family occurrences in Clause2
  CandidateC2 = conjunction/family of C occurrences in Clause2
  CandidateP2 = conjunction/family of P occurrences in Clause2
  Inc2 = composition of the actual IF-Insert, IF-Use, operand and event maps

The conjunction/family notation means the actual finite registered graph with its original conjunction/reference constructors, not universal quantification over an unspecified “all guards”. Imported and primitive clauses enter only through their actual declaration insertion and use, with their whole independent T_q and predicate R_q. No new provider or observation is synthesized by S-F2.

S-F2 is a proposed rule schema, not an existing source rule. The current inputs establish root allocation, selected contextual assembly and IF placement under their own scopes; they do not establish the required Clause2 partition or its equality with the original I2. Therefore CandidateI2 is not identified with original checked admission until the occurrence inventory and phase owners are adopted/proved.

## 4. Concrete clause families and phase formulas

The prior reviewed guard ledger supplies twelve *families to audit*, not twelve established F2 occurrences. For each actual q, use the original predicate projection pi_q from the full joined telescope. A clause is present only if the original source owner supplies that occurrence.

| Family | Candidate formula at its owning occurrence | Phase and source placement |
|---|---|---|
| G01 context/environment | A_q(e,h,k) := CompatibleContext(C_e,w_e,h,k) | Admission prerequisite at original checked challenge; retain valid other bindings and hypothetical callable hole. |
| G02 registered holes/incidence | A_q := Registered(h,k) AND ActualUseMap(u,q,m) AND TypedPathMap(q,u) | Admission prerequisite only for actual registrations/references; IF-Use carries the real m, not membership or receipt. |
| G03 scope/license/captures/profile | A_q := WellScoped(T_q) AND OriginalLicense_q AND CaptureClosed_q AND ProfileFormed_q | Admission/formation prerequisite at its declaration; license truth remains its own source contract. |
| G04 whole carrier | C_q := Form(U,e) AND FORALL delta in Dem(k,h), FORALL O in Obs(k,delta), T_U(delta,O) | Carrier formation/observation after a carrier is supplied; cannot be moved into A_q by successful execution. |
| G05 guarantee bounds | C_q := FORALL (delta,O) in original fiber, OriginalGuarantee_q(T_q,delta,O) AND JointBounds_q(T_q,delta,O) | Carrier observation at its actual demand/event; retain equations and support, do not add an empty-effect assumption. |
| G06 admission-dependent provider typing | A_q := OriginalPreEntryTyping_q(actual provider interface, whole carrier, shared context); C_q/P_q := original event/output clauses at their own events | Split by actual source phase. Acc(J_U,k) from later membership is never an A_q premise. Exact F2 occurrences remain open. |
| G07 K atoms | A_q/C_q/P_q := conjunction of the original K2 atoms whose owner phase is pre-entry / carrier event / output event, each on the same projected T_q | Retain every actual atom and its joint witness; “K is valid” is not a replacement clause. |
| G08 D atoms | A_q/C_q/P_q := conjunction of the original D2 incidences with original endpoints and source positions, split by owning event | Keep correlated endpoints and original identity; no per-port witnesses. |
| G09 entry/authority | A_q := OriginalEligible_q(e,entry,receipt-prerequisites); C_q/P_q := LiveAuthority_q only at the actual later Observe/Receive event | Admission eligibility is distinct from a later live grant; no origin-to-live-authority inference. |
| G10 response/resumption/future | C_q/P_q := FORALL admitted request, response, raw handle, ordered suffix, resumed state and future event, preserve original dependent event and world | Carrier/invocation behavior at its actual event. Any independently declared pre-entry domain clause remains A_q only at its real occurrence. |
| G11 independent W/Z/opaque alternatives | C_q/P_q := conjunction of each actually inserted alternative R_q over its complete output-provider/future telescope | Preserve unanchored alternatives and changed coordinates. Do not infer an A_q clause from source reachability or remove a clause lacking source execution. |
| G12 parameter/domain actions | Inc2 includes each original lawful scoped action map; for any changed-domain clause require its declared total/domain certificate | Formation/transport premise, not a filter on successful carriers. No forward-only or positivity shortcut. |

The displayed equations fix the proposed *shape* and event placement of each family; each R_q and each parameter/domain action must still be the real original declaration or an explicitly proposed new clause. The family ledger does not establish that original F2 contains exactly G01–G12. In particular G04/G05/G10/G11 generally describe carrier or invocation obligations rather than admission. Copying them into A2 would change behavior.

The pending source decision is concrete: for each newly proposed pre-entry occurrence q, choose either (i) include its explicitly displayed A_q relation, thereby rejecting any tuple that violates it, or (ii) retain q solely in C_q/P_q at its actual later event. Moving a C/P clause into A2 changes which carriers the original checked inlet accepts; omitting a genuine A_q changes admission. The table names the coordinate and consequence but does not select either branch where the source owner is missing.

## 5. VIEW and CHECK obligations after construction

Only after an adopted/proved S-F2 rule can the proof lane ask:

- VIEW: from original I2 admission at the same telescope, derive carrier formation, every target (delta,O) in full B_in, and each actual A_q projection through its authentic IF occurrence. Target-domain coverage must be total; endpoint equality or four-port projection alone is insufficient.
- CHECK: from full B_in evidence plus every actual A_q at the same correlated tuple, derive original I2 admission. Every A_q must be jointly witnessed with the same context, root, provider and event. Do not assume ValueMem_F2, Acc(J_U,k), Q, a desired result, or successful comparison.
- C/P clauses remain in their actual observation/result phases; a CHECK premise cannot fabricate them before an actual output or event exists.

Current source definitions do not give the complete Clause2 set, its event partition, or an equality between CandidateI2 and original I2. The exact first missing premise is an owner-supplied occurrence/phase map, followed by any genuinely new A_q meanings requiring adoption. This is a decision-ready gap, not closure of either inclusion.

## 6. Parent application, limits and implementation route

This candidate supplies a shape for a source producer and a concrete audit ledger; it does not prove S-F2 can be applied at original c2. The original A/B theorem still independently needs full A1/provider/context/world/future coverage, source T, native MODEL, complete descriptor embedding, all original guards and the reviewed semantic inputs. The selected bounded Value-entry control correspondence remains a separate runtime-order result and contributes no admission clause.

The current candidate_source/candidate_call/candidate_scheme/shadow_apply owners retain some source and native incidences but do not generate this complete original admission contract. There is NO_SAFE_CODE_SLICE for this gap. A future implementation would need an adopted source rule, verified generation/propagation/consumer alignment, principality and expected-output review, plus a separately authorized code lease. No code edit, test, build, probe, runtime execution, expected-output change or semantic adoption occurred here.

## 7. Exact remaining owner requests

F2-ADMISSION-PRODUCER: source declaration/definition/use Function-view owner must provide or decide the complete actual q occurrence set, its A/C/P phase tags, primitive/import inclusion rule and each scoped operand telescope. Falsifier: an omitted original pre-entry occurrence, an invented occurrence, or a clause moved across event phase changes admission.

F2-VIEW: original Function source-generation/descriptor owner must show every original I2-admitted tuple and each complete B_in target (delta,O), including full typed incidence and actual A_q projections. Falsifier: one uncovered target or one changed original domain.

F2-CHECK: original whole-argument-checking/descriptor owner must derive the same I2 at the original tuple from full B_in evidence and the jointly witnessed, exhaustive A_q family. Falsifier: one admitted tuple violates an A_q, or any A_q is supplied from Q, membership, provider success or output.

All three remain OPEN. This proposal is unselected and is not independent review.
