# CALL_TYPE: operand-context clause candidate

Date: 2026-10-07
Baseline: `6cd43ea855acdd1e7f47a46408715a03d192ffd4`
Status: independently reviewed research-only candidate; no semantic adoption
Method: constructive finite clause schema for the captured Name/Return cut
Exclusive lease: `notes/progress/2026-10-07-call-type-operand-context-clause-candidate.md`
Authority/implementation: none

## Objective and exact result

Make the ordinary operand premise precise enough to derive

```text
DescMem(Comp(empty,A_f), Return(lookup f,C), w;xi)
```

for the captured outer `f` in the approved
`my apply f = { my step x = f x; step }`. The package below supplies a
**candidate assumption** about typed environments, a proposed Return rule,
and an explicit whole-carrier Delay bridge. Under those assumptions it gives
a **conditional derivation** of this operand cut. It does not prove the
assumptions, all of CALL_TYPE, joint interpretation, source adequacy, or
production containment. Its finite scope is seven clause schemas, not a bound
on caller contexts or finite histories. No language meaning is selected here.

The reviewed fixed-cut reconstruction already accounts for the operational
branches and identifies this premise gap. This note changes method: it proposes
the missing semantic conjuncts and last rule instead of another transition
probe or another model with unconstrained descriptor predicates.

## Governing sources and approval boundary

Read at the pinned baseline:

- [Fixed-cut reconstruction](2026-10-07-call-type-fixed-cut-reconstruction.md),
  especially “First unavailable constructor rule” and its final premise audit.
- [Inlet q1/d1](../../questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md)
  decision items 1–5 and its receipt: all independently well-typed compatible
  punctured contexts at the original tuple, direct callable and whole carrier
  holes, other bindings/import validity, Q independence, and no mandatory
  source-constructor witness. Exact environment/admission rules remain open.
- [Formation q1/a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md)
  items 1–6 and its receipt; the corresponding Authoritative inferred-call-view
  §§1–5: one source-owned correlated view, actual role/entry distinct from the
  internal formal view, typed paths from source elaboration, not comparison.
- [Bound-membership q1/d1](../../questions/2026-10-05-production-function-bound-membership/approved-answer.md)
  items 1–4 and receipt: Option 2 extras allowed; an exhaustive concrete
  membership grammar and complete containment remain unselected.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§3,6,9: inert descriptors/Delay, ordinary Name/Normalize, actual entry and
  complete ordered invocation. This document remains Draft; these equations
  are used conditionally at their reviewed scope, not promoted to authority.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2,3.2–3.5: independently typed kernel inputs, active descriptor
  conjunct, same-tuple constructors, independent histories and conditional
  realization. They assume local typing rather than derive it.
- [Nested-source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3 fixes this exact source and capture identity, not semantic membership.
- Canonical DAG nodes CALL_TYPE, DESC_CLAUSES, ADMISSION_CLAUSES, SEM_JOINT:
  respectively OPEN-PROOF, OPEN-SEMANTIC, OPEN-SEMANTIC, OPEN-PROOF.

The approvals entail the preservation requirements and quantification scope.
They do **not** entail the candidate equations C1–C7 below. In particular,
approval that a context must be independently typed does not define the typing
judgment. Accepting the broad domain does not grant a Return rule.

## Fixed coordinates and judgment meanings

Fix the original `X`, binder tree, `xi=(nu,K,D)`, interface graph, captures,
provider roots and source/view incidences. A single witness `eta` assigns their
whole tuple, including runtime lexical references, actual providers, world,
operation instances, paths, origins, authority, scopes, and correlations.
Do not choose a new witness independently for each binding or phase.
Metatheoretic witnesses add no source existential type or runtime object.

For this candidate, `Val_A(v,r,w;eta,xi)` is the ordinary independently
interpreted **whole value/provider judgment** at original root `r`. It includes
the value descriptor at `A`, its actual provider/capture incidences and all
latent eliminations required by that descriptor. If `A` is Function, those
include its actual role, entry and designated consumer, plus its independent
future-use contract. If `A` contains a computation or raw continuation, it
includes the corresponding latent typed port or original handle obligations.
This is a proposed semantic premise sort, not a definition by Name syntax,
solved shape, source execution, or successful Q. Its complete clauses and
common realization remain DESC_CLAUSES/SEM_JOINT obligations.

`JointWF_X(w;eta,xi)` names the independent current-world judgment for the
entire original tuple: every accessible root/import, scope, authority, alias,
operation/response incidence and raw handle/current store is coherent. It
must be interpreted jointly with Val/DescMem/CarrierMem. This note does not
choose its mutable-store or import laws, nor assume an inhabited valid world.

`Inc_X` below abbreviates the retained original lookup/capture/provider/path
and cross-port evidence. It supplies no original slot/contribution attachment
or licensing rule. `C=current(w)` always means the actual current
configuration, including current resumed state, not a captured state snapshot.

## Seven proposed clause schemas

All seven are NEW proposals for the relevant semantic clauses. Structural
equalities inside C1/C3/C6 and the preservation restrictions are already
recorded; their semantic membership consequences are proposed here.

### C1. Ordinary lexical environment

For a finite lexical binding map with ordinary Value bindings, propose

```text
Env_X(Gamma,rho,w;eta,xi) iff
  JointWF_X(w;eta,xi) and Inc_X(Gamma,rho;eta,xi)
  and for every y in dom(Gamma), Gamma(y)=Value(A_y):
      rho(y)=eta(r_y)
      and Val_A_y(rho(y),r_y,w;eta,xi).
```

Each `r_y` is the already resolved original lexical/provider root. Dependent
providers and aliases use that same `eta`; they are not a product of separately
valid values. Capturing `f` preserves `r_f` and `rho(f)`, including aliases.
Environments containing retained Computation bindings additionally require
the corresponding whole CarrierMem judgment at that binding's original port;
this extra case uses C5 and does not retag it as Value. For a recursive finite
provider graph these equations reference registered roots without unfolding.
This is a simultaneous specification; it asserts no least/greatest fixed point.

### C2. Compatible punctured context and filling

Let `Cminus` be any independently typed punctured caller context with direct
callable hole `H_f` and whole-carrier hole `H_t`. Its certificate checks the
context's own structural rules under those hole interfaces and retains the
original `Inc_X`, correlations and scope. Hole assumptions are discharged by
the same filling witness, never by proving the pending Function comparison.

Propose the filling condition

```text
FillOK_X(Cminus,actual_f,t,rho,w;eta,xi) iff
  CtxMinusTyped_X(Cminus;Gamma,H_f,H_t,eta,xi)
  and EnvOutsideHoles_X(Gamma,rho,w;eta,xi)
  and Val_A_f(actual_f,r_f,w;eta,xi)
  and CarrierMem_R_t(t,r_t,w;eta,xi)
  and Compat_X(H_f,H_t,actual_f,t;eta,xi).
```

`EnvOutsideHoles` is C1 on all other bindings/imports; aliases incident to a
hole are checked against its filled root, not deleted as “outside”. `Compat`
requires the actual provider's role/entry/consumer, original argument port,
receiver/receipt path, origin, continuation, authority, scope and joint
dependencies to meet the declared receiving contract. Any required conversion
must have its independent whole-contract certificate. Matching endpoint shapes
alone are insufficient. The receipt path is statically valid before execution;
C2 does not claim the receiver is already dynamically activated.

The proposed domain is **all** such certificates/fillings, including other
programs, currently unreached uses, composition and later reuse. No source
execution witness, pending Q, checked containment conclusion, TypedCallCert
with original attachment, or current-source reachability is a conjunct.
`CtxMinusTyped` is an independent judgment to be specified and justified; this
schema does not make typing decidable or supply its rules by naming it.

### C3. Name elimination

```text
Env_X(Gamma,rho,w;eta,xi), Gamma(f)=Value(A_f), lookup(f)=rho(f)
  => Val_A_f(lookup f,r_f,w;eta,xi).
```

This implication follows by conjunct elimination **if C1 is adopted and
realized**. It does not follow from `Gamma(f)=Value(A_f)` alone. The same
rule applies separately to `x` at its own `r_x` and `A_x`.

### C4. Return introduction with latent preservation

```text
JointWF_X(w;eta,xi), Val_A(v,r,w;eta,xi), C=current(w),
the ordinary Return relation returns exactly (v,r,C) with its retained evidence
  => DescMem(Comp(empty,A),Return(v,C),w;xi).
```

The proposed returned-provider conclusion is the same `Val_A(v,r,w;eta,xi)`
at the outward original typed port, with all required latent future-call,
force and raw-handle obligations. Return does not execute them, freshen their
binders, weaken their grants, or substitute captured state for current state.
`empty` constrains this Return computation's execution effects; it does not
assert a returned callable/computation has empty future effects. C4 is an
introduction rule only, not an exhaustive Return/Request descriptor definition.

### C5. Independent whole-carrier criterion

Propose a constructor-independent criterion

```text
CarrierMem_R(t,r,w;eta,xi) iff
  InertCarrierWF_R(t,r,w;eta,xi)
  and for every independently admissible designated demand at (r,w')
      compatible with this same eta,xi and retained captures:
        every complete or pending observation O of one-layer Force(t)
        satisfies DescMem(R,O,w_O;xi), with joint world/provider preservation.
```

`InertCarrierWF` requires the whole inert value, original typed view, origins,
captures, scope, authority and dependencies; it does not require `t=Delay(J)`
or a source-constructor derivation. The demand domain has independent
Init/Response/Resume/FutureUse clauses, at the current world and original raw
handle. It includes divergence/prefixes and latent returned providers as
required by R. No return observation is required for admission. “Every” is
unbounded over allowed finite developments; an empty domain or an empty
execution set supplies no inhabitance result. A realization must rule out any
unintended vacuity rather than treating this formula as proof of valid inputs.

This candidate is deliberately not membership defined as the source image:
source-produced Delay is only one introduction case. Option 2 carriers and
observations can satisfy the same independent criteria without a source witness.
The proposal's adequacy for all production observations remains unproved.

### C6. Delay introduction

Define a semantic code certificate `RunCert_R(J,rho;eta,xi)` to mean that every
raw complete/pending execution of J, at every independently admissible current
demand world compatible with these retained lexical references, has the C5
descriptor/world/provider consequences. This is a universal semantic premise;
calling it a certificate does not derive it from source syntax.

```text
RunCert_R(J,rho;eta,xi),
Delay(J,rho) preserves the original lexical references and inert-carrier evidence,
Force(Delay(J,rho),current(w')) = Run(J,rho,current(w'))
at each independently admissible designated demand
  => CarrierMem_R(Delay(J,rho),r,w;eta,xi).
```

The implication is substitution into C5 if its independent demand domain and
inert evidence are satisfied. Construction performs no execution, no receiver
receipt and no entry force. Future valid demand requires the captured bindings
still have C1's judgments at **that current world**. Capture identity alone
does not prove this transport. No new capture-lifetime/world law is inferred.

For `J_x=Return(lookup x)`, C3/C4 at every such demand world give RunCert for
`Comp(empty,A_x)` conditionally on that world/environment preservation.
To pass the resulting Delay at a different required receiving view `R_t`, C2
still requires an independent whole-carrier compatibility certificate; endpoint
equality is not that certificate. The generic hole can contain effectful or
divergent admitted carriers even though this particular Name diagonal is pure.

### C7. Saved-suffix requirement on pending observations

Any use of C4–C6 at an enclosing Bind must retain the full actual remaining
suffix. The required independent pending judgment is on the composed handle:

```text
Request(q,C,k) >>= S = Request(q,C,k >>= S).
DescMem(R_pending,Request(q,C,k >>= S),w;xi)
```

Its response/resume clauses must type every admitted continuation development
at the same operation/response witness and current resumed state, including S.
Typing k alone is insufficient. For callee pending prefixes S contains argument
construction plus receipt/entry/body/designated consumer/return; entry pending
prefixes contain rebind/body/consumer/return; body/consumer pending prefixes
retain only their outstanding shell. Completed phases are never replayed.
The exact Name callee has no executing Request prefix, but C7 cannot be omitted
from generic CALL_TYPE or whole-carrier C5. This is a proposed obligation shape,
not a proved Bind rule; actual closure and operation consumers remain distinct.

## Conditional derivation of the exact operand cut

Assume one common interpretation satisfying C1–C7 and the original independent
world/admission family. No interpretation or admitted filling is constructed.
Take any independently admitted filling that supplies C1 for the captured
lexical environment. The approved source identity gives the same original
`r_f` and lookup; typed-core §6 gives `Gamma(f)=Value(A_f)` and
`Normalize(...)=result(name f)`; §3 gives `J_f=Return(lookup f)`.
C1/C3 yield `Val_A_f(lookup f,r_f,w;eta,xi)` and JointWF. C4 therefore yields
the displayed `DescMem(Comp(empty,A_f),Return(lookup f,C),w;xi)` with its
latent/provider evidence intact. This is premise elimination followed by a
proposed introduction rule, not a proof that approved lexical identity entails
membership.

The same steps at x plus C6 give its inert Delay only if valid-world transport
and all-demand RunCert premises hold. This derivation stops before actual
receiver entry, rebind/body/consumer typing and pending-Bind closure. Those
cannot be obtained by strengthening this operand premise to contain the desired
complete Call conclusion. No original slot/contribution witness is introduced.

## Failure conditions and unresolved alternatives

1. If the intended independent operand premise already supplies C1's Val/world
   conjuncts, C3 is elimination; C4 still needs its own descriptor clause.
   If it supplies only lexical identity and interfaces, the candidate is a
   genuine semantic strengthening requiring approval, not an editorial repair.
2. If C4 conflicts with ordinary latent-provider or world membership, reject or
   repair its side conditions. Do not weaken A, erase latent obligations or
   define DescMem to accept the generated observation by construction.
3. If compatible demand worlds can invalidate captured evidence, supply the
   original capture/world-preservation rule or narrow only the independently
   justified compatibility condition. Do not restrict the approved domain to
   current-source reachability or silently reuse creation state.
4. If C5 excludes independently valid Option 2 production carriers or pending
   observations, this proposal is incomplete; extend its semantic clauses and
   prove the bridge. Do not require a source witness as an expedient fix.
5. Recursive Function/Carrier/Desc/world predicates are mutually dependent and
   can have mixed variance. The equations do not select a fixed point, establish
   consistency, independent admission completeness, nonvacuity or inhabitation.

Recommended next action: independently review C1/C4 as the precise new
operand/Return semantic decision, then present that boundary for user approval;
retain C2/C5–C7 as explicitly conditional downstream proposals until their
admission, latent and joint-realization obligations are resolved. No gate closes.

## Checks, independence, coverage and resources

Static source/approval reading and baseline byte/hash comparison only. No
Oracle, checker, tests, builds, executable experiment, mutation run, seeds,
enumeration range, performance samples or Git mutation. Hypothetical mutations
that erase Val from C1, erase latent obligations from C4, require source witnesses
in C5, use capture-time state in C6, or shorten C7 would attack named premises;
they were not executed. There is no minimized counterexample claim.

The operational bridge shares the reviewed candidate-core equations. Its
conditional derivation is logical substitution, not an independent oracle for
their source meaning. Two implementations of those equations would not certify
C1–C7 or SEM_JOINT. At the producer handoff, independent review had not yet
occurred; its later outcome is recorded in the review adjudication below.

Early aggregate read captures were truncated; the exact governing core,
contracts, approvals and DAG nodes were reread in bounded extracts. No full
repository search, absent-rule theorem or exhaustive production grammar audit
is claimed. No `spec/` directory exists at this baseline; relevant specification
material here is the cited design/approval sources. Other research attacks were
not repeated, and no other worker's unfinished output is a dependency.

Resource limit: 15 minutes static work, zero heavyweight/experiment processes.
Actual CPU/peak RAM and exact elapsed wall time are unmeasured; read/hash commands
were short-lived, with at most three concurrent lightweight read commands.
Changed path: this note only. Source formation, recursive generalization,
opaque imports/mutable-world rules, all complete descriptors/admission cases,
joint realization, actual-world inhabitance, production containment and
principality remain unverified.

## Dependency snapshot and commit packet

All twelve semantic/review dependencies matched baseline bytes immediately
before writing; SHA-256:

```text
c9f174dc8d5209f0415b062747d40873d60ee7f679a9b14388eddce8fa15768c notes/progress/2026-10-07-call-type-fixed-cut-reconstruction.md
1b4d27e80fb8437fc78adde55853cdbd7b5cc0a9e819c7eb3474dc83a09aeeb3 notes/theory/successor-proof-obligations.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e notes/design/2026-10-02-typed-computation-core-elaboration.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186 notes/design/2026-10-05-source-contracts-and-common-allowance.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0 notes/design/2026-10-06-nested-block-function-source-realization-addendum.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3 questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
a952c4588f6020ba1c51f69c623bf12ef695d73fe086496bf6ecdeee37450021 questions/2026-10-05-production-function-inlet-context-domain/receipt.md
1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536 questions/2026-10-05-function-call-view-formation/approved-answer.md
6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0 questions/2026-10-05-function-call-view-formation/receipt.md
d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179 questions/2026-10-05-production-function-bound-membership/approved-answer.md
f69a924b52e0cfb198df62a33e7e5c358ee1d0799ecf7c16cf32b9f8cb2f7e98 questions/2026-10-05-production-function-bound-membership/receipt.md
```

- Exact leased path: `notes/progress/2026-10-07-call-type-operand-context-clause-candidate.md`.
- Baseline SHA: `6cd43ea855acdd1e7f47a46408715a03d192ffd4`.
- Dependency changes: none at pre-write comparison; primary must revalidate
  against the frozen artifact before review/integration.
- Claim at handoff: candidate semantic clauses plus conditional operand
  derivation; then unreviewed and research-only, with no approval or theorem
  closure. Independent reviews and current disposition are recorded below.
- Checks already run: governing reads, pinned HEAD confirmation, lease absence,
  twelve baseline byte/hash comparisons. No semantic execution.
- Proposed commit: `research: propose Call operand environment and Return clauses`.
- Shared-record deltas left for primary/curator: optionally link the candidate
  and record C1/C4's approval boundary; keep all four gate statuses unchanged.
  No shared task/index/theory/authority, question-board, code, test, manifest,
  lockfile or other worker path was edited. Writes stop at this frozen handoff.

## Independent review adjudication

The frozen candidate content above was reviewed at SHA-256
`15aff1db04ef28572ab849d58f019e025ee4ed2120e3df11754a71c362bb6b5f` by one
compiler referee and one spec auditor. Both reported no blocking, major or
minor findings within the explicitly research-only scope. The referee found
the conditional Name/Return derivation, broad punctured-context domain,
Option 2 allowance, joint-witness boundary, current-world Delay obligations,
saved suffix, vacuity caveats and approval boundary correctly exposed. The
spec audit found C1–C7 consistently labeled as proposals rather than adopted
clauses and confirmed preservation of the approved inlet and call-view
constraints.

Disposition: retain as a reviewed conditional research candidate. Neither
review supplies approval for C1–C7, a common realization, inhabitance,
admission completeness, or any closed theorem. `CALL_TYPE`, `DESC_CLAUSES`,
`ADMISSION_CLAUSES` and `SEM_JOINT` remain open. Any future semantic adoption
requires explicit user approval and a new proof/adequacy review of the
selected clauses.
