# Admission A for the exact captured-step component

Date: 2026-10-06
Baseline: `b0dd026bb9438b7dfb13c68a474a49145eb97555`
Status: frozen unreviewed research; conditional derivation and bounded premise localization
Implementation and semantic authority: none
Exclusive lease: this file only
Method: source-constructor derivation at the two successive Value-entry cuts

## 1. Objective, authority and claim classes

Attempt independently typed initial punctured-context admission for exactly
`my apply f = { my step x = f x; step }`, after the reviewed source-call
construction. The source meaning is already selected: the block returns the
local closure, which captures the same outer `f`; it does not call `step`.
No alternative block meaning or inferred-role interpretation is explored.

The [source-call construction](2026-10-06-source-call-generation-construction.md)
§§3, 5–7 and its [review](2026-10-06-source-call-generation-review.md) establish
the initial static Call address and interpreted existential decorated Call
constraint. They leave P (original full profile) and A (initial independent
context) open. This note treats P as an explicit input to A; it does not
construct P or equate its full slot inventory with the initial singleton.

Exact governing clauses are:

- [Nested-source addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3 and [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1.1–4: source identity/capture, shared inferred root, provisional seed and
  ordinary-value refinement, annotation absence and comparison independence.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3.5, 3.7, 10: independently interpreted joint primitives, decorated
  source envelope, four independent admission cases and conditional coverage.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§6, 9: syntax-directed Value entry for both unannotated parameters,
  inert whole arguments, entry/rebind/body/consumer, and the joint domain law.
- [Source-interface adequacy](../design/2026-10-02-source-interface-adequacy-theorem.md)
  §§2–4: admissible assignments/contexts as inputs, exact relational images,
  finite future interactions and raw-resumption fidelity.
- The committed approved `production-function-inlet-context-domain/q1/d1`,
  `production-function-denotation/q1/d1` and
  `production-function-bound-membership/q1/d1` answers: all independently
  compatible punctured contexts at fixed original `xi=(nu,K,D)`, directly
  supplied callable and whole carrier, independent surrounding values,
  Option A/2 and no universal source-constructor requirement for members.

**Established inputs:** the selected source skeleton and reviewed Call slice.
**Conditional theorem below:** a reached source Call has a specific returning
Name carrier and the same captured provider, assuming independently typed
inputs and the supplied decorated realization kernel.
**Candidate relation:** independent admission expressed by a two-hole context
judgment whose atomic interpretation is not supplied here.
**Bounded characterization:** the inspected sources do not discharge that
judgment. No unconditional admission theorem, production counterexample,
necessity of a new user decision, or carrier insufficiency is claimed.

## 2. Construct the exact source cuts before asking admission

Write `T_f` for the whole carrier supplied to `apply`, and `T_x` for the
whole carrier supplied on a later invocation of its returned `step`.
These are different from the inner Call argument `J_x`.
Typed-core §6 generates, before body synthesis:

```text
P_apply = Value(A_f)       Gamma(f) = Value(A_f) after entry
P_step  = Value(A_x)       Gamma(x) = Value(A_x) after entry
c = call(result(name f), result(name x))
J_x = ReturnImage(Name(d_x), original environment)
printed interface(J_x) = Comp(empty,A_x)
```

Let `EnterReturn(T,C;v,C')` denote an actual finite entry development which
returns `v` at `C'`, including any intervening matched request/resumption
developments. This notation makes no new admission test: its developments
must already have independently typed responses, original raw handles and
valid current configurations in the decorated source kernel.

Suppose independently typed `T_f` has an `EnterReturn` to `v_f,C_1`.
Apply's body then constructs the inert local closure with capture
`rho_step(d_f)=v_f`, binds it and returns that same closure. The body of `step`
has not run. On a later independently typed invocation, suppose `T_x` has an
`EnterReturn` to `a,C_2`. Entry rebinds `d_x` to `Value(a)` before the inner
Call. Consequently that inner Call constructs exactly

```text
callee = rho_step(d_f) = v_f
whole inner carrier = Delay(ReturnImage(Name(d_x),rho_step[d_x:=a]))
```

Operationally the inner Name reads and returns `a` in its current context;
it does not replay `T_x`. The source tags/provider roots and packet dependencies
remain present even though the carrier has a returning Name image.

**Conditional cut lemma.** Fix one admissible original `xi`, original scopes,
the P-generated profile, independently typed entry inputs and the source
realization premises. Every reached inner Call has the displayed provider
and carrier at the original typed cut, with that same `xi` and all live
dependencies. It need not already have the inner callee's executed receipt.

**Proof.** Outer Value entry executes `T_f` once and rebinds its result.
Lambda construction stores the resolved environment without executing its
body. Bind/Result return its closure while preserving the capture. Step's
Value entry executes `T_x` once and rebinds its result. The two Name rules
then read their respective resolved roots, and Call reifies the whole inner
argument inertly. Each request in either entry retains its original operation
witness and raw continuation; stateful Bind appends the pending rebind/body/
return suffix and threads the current resumed state. Source-interface §4's
invariants preserve the joint `K,D` incidence and original ownership through
each step. Induction on these finite supplied developments proves the cut
claim without testing `Q_pending`. No expired handler is reinstalled by the
argument. QED, conditional on the displayed typing/realization inputs.

This yields static source construction without first choosing a satisfying
instance. It yields a reached cut only when the stated entry developments
exist. It neither proves there is an admissible complete `xi` for every
generated constraint set nor proves that every possible carrier returns.
A divergent `T_f` can prevent closure return; a divergent `T_x` can prevent
the inner Call. Both have finite-prefix behavior; neither is excluded from
the approved broad inlet domain merely for divergence.

## 3. The original joint tuple can be preserved, but not manufactured

On the conditional route above, choose nothing per port. One tuple `w`
contains the original source endpoints, captured provider, argument root,
current configuration, profile, continuation and live evidence at `xi`.
Every local constructor consumes its incident coordinates of this same `w`.
The only hiding is at each original binder position after conjunction:

```text
R_reached(xi,h0) = exists_original_scopes w.
    TypedSourceEntryInputs(w;xi)
  & ApplyEntryBodyReturn(w;xi)
  & ReturnedStepEntry(w;xi)
  & NameCallCut(w,h0;xi)
```

This relation preserves the shared source root `d_f`, including capture and
later lookup. It is not the intersection of projections with independently
chosen provider, carrier, configuration or `xi` witnesses. Under a rigid
binder each dependent witness stays within that binder.

`TypedSourceEntryInputs` is a supplied independent typing premise, not a
rule synthesized by naming this formula. Thus this proves propagation of an
original joint assignment when given; it does not derive its admissibility
from lexical resolution or the existence of a compatible decorated instance.
Likewise the source rule determines which carrier reaches this cut; it does
not say that all values with printed `Comp(empty,A_x)` have that exact image.

This distinction is specific to this candidate's two successive entries.
The previous generic
[puncturing attempt](2026-10-06-production-function-admission-constructor-attempt.md)
already isolated `PCInit`; this note does not repeat its receipt-inversion
control or its Unit witness. It identifies the narrower returning-Name image
which any attempt to extract A from this exact program must cross.

## 4. Why source-reached cuts do not give the selected inlet domain

The approved domain includes contexts not reached in this program, contexts
from other programs, composition and future reuse. Direct insertion of the
whole callable/carrier is required; surrounding values must still be
independently valid and correlated. Therefore enumerating `R_reached`, or
all traces of this exact `step`, cannot establish exhaustive A. The original
program's inner carrier image is only one source-reached subcase.

A generic challenge carrier may request or diverge before returning its
eventual `A_x`. Whether a particular such carrier is compatible depends on
the missing independent inlet contract, not merely its eventual result type
or absence from this program's reachable cuts. The cut lemma does not prove
that any effectful carrier belongs to a particular completed `F_c` domain,
or that the broader and narrower domains yield different accepted programs.
No selected endpoint instance or comparison success is used to assert such
a discriminator.

Separately, Option 2 allows independently licensed complete production
members without source-constructor evidence. Source-reached membership cannot
serve as their admission grammar. Source-contracts §3.7 explicitly needs
admission/provider certificates for such alternatives; membership positivity
does not generate those certificates.

## 5. The minimal remaining independent judgment on this route

With P supplied, the unresolved premise can be stated at the pre-invocation
cut, without assuming an executed receipt:

```text
OpenInit_sigma(xi;
    H_f : declared F_c at original beta,
    H_arg : whole carrier at its original input path;
    kappa, eta_except_holes, carrier, current_configuration,
    original result/consumer path, capture/source incidences)
```

Its necessary obligations are concrete:

1. A source context is typed with the two declared holes. Its constructor
   rules use their declared interfaces and original incidences, with no
   premise that the tested callable already satisfies the compared bound.
2. Every other free value/import is independently valid under the same
   original `xi`. If a retained capture aliases a hole, that alias/root/path
   equation remains in the shared tuple. Holes are not free permission to
   combine unrelated providers or states.
3. The **whole** carrier has an independently interpreted inlet/path/contract
   relation to the declared parameter, including continuation, origin, scope,
   authority, role and live `K,D` constraints. Eventual result typing alone
   does not supply this relation.
4. The current configuration and typed result consumer/path belong to that
   same independently typed context. Static P-profile compatibility precedes
   future receipt; future receipt must realize the same original incidences.

Independent validity of a supplied callable at its original environment root
may be necessary. It must not be silently replaced by membership in the bound
currently being compared. The tested filling's private proof is not an input
to the hole-typing rule. This distinction keeps the environment condition
from recreating `Q_pending`.

A candidate initial relation is then

```text
A0_candidate(beta,h0;xi) = exists_original_scopes kappa,eta,w.
    OpenInit_sigma(xi; H_f,H_arg;kappa,eta,w)
  & OriginalHoleIncidence(beta,kappa,w)
  & InitialCutTuple(kappa,eta,w,h0)
```

These last two factors copy/check the original correlated addresses and
extract the cut; they neither compute slot applicability nor create admission
from a successful invocation. The existential ranges over independently
typed contexts, not over favorable instances chosen to make `Q` succeed.
This formula is a **candidate assumption with an unprovided constructor**,
not a completed rule. Minimality here means the residual input interface after
the displayed source constructors, assuming P; no theorem excludes other
formalizations or proves a cardinal-minimum axiom basis.

## 6. Why the existing clauses do not discharge OpenInit

| Clause | What it provides | Remaining input |
| --- | --- | --- |
| Selected nested source and typed-core §6 | Resolved captures, fixed Value-entry tags, Name/Bind/Lambda/Call skeleton | Independent world/import validity and whole-carrier compatibility |
| Reviewed Call constraint, §5 | An independently meaningful existential constraint over the decorated basis | `TypedCallCert_Dec` and admitted execution domain, not its source reconstruction |
| Source-contracts §2 | Interpretation on a joint fiber and active retained roots | Independently specified local primitives and owner/view kernel |
| Source-contracts §3.3 | Initial, response, raw-resume, future-use inventory | Initial source context is already typed; the inventory does not construct that typing |
| Source-contracts §3.5 | Bidirectional finite derivation translation | §2 and the full finite conformance/local typing certificate, including admission |
| Source-interface §§2–4 | Execution and exact interface simulation preserving supplied typing | Admissible `nu`, initial typed configuration and future-interaction admission |
| Typed-core §9 domain law | Sufficiency of joint domain inclusion and observation inclusion | Both domains and their inclusions are input propositions |
| Source-contracts §3.7 | Conditional production extras and transport | Independently supplied abstract primitives and unchanged/changed-domain certificate |

Supplying `OpenInit` plus independent response/resume/future-use constructors
would permit a finite-history induction: initial uses its cut certificate;
response retains the exposed request witness; resume uses its actual raw
handle/current state; future use retains the returned provider's typed port.
All constructors preserve one `xi` by hypothesis and the source equations.
This is a conditional history theorem, with no fixed horizon or need to
assume termination. It proves neither those constructors nor completeness of
their production interpretation. In particular future uses after a production
extra require the extra's independent provider/history rule.

The precise blocker is therefore an independently interpreted two-hole
context/environment and whole-inlet judgment at the P-generated root.
No amount of expanding the same source execution trace or checking its own
transition rules supplies that missing premise. Two earlier routes already
stopped there; this lane stops after the exact-cut derivation instead of
running another equivalent toy model.

## 7. Verification, independence, resources and exclusions

No executable oracle, search, mutation experiment, compiler test, build,
formatting, child agent or Git mutation was used. There are no seeds/ranges.
The proof deliberately shares the source/decorated constructor equations
with its source-interface argument; it is not an independent validation of
those equations or current production. The claim is their explicit
conditional consequence and a bounded dependency audit.

Commands run: narrow `cat`, `sed`, `rg` reads of the named rules/sources;
`git rev-parse HEAD`; Python SHA-256 and `git show <baseline>:<path>` equality
checks for the seven direct source dependencies and all twelve files in the
three approved bundles. Every dependency checked equals the pinned baseline.
Some combined read output was truncated; relevant exact sections were reread
in smaller captures. The absent `spec/` directory was reported by `rg`; no
claim of complete specification or repository search follows.

Local process usage was sequential lightweight read/hash commands, no
heavyweight process or numerical measurement. CPU/RAM peaks were not measured;
each returned command session was below one second. Wall time is recorded
in the final worker report where available, without a fabricated budget.
No separate resource budget was provided beyond no builds/tests/Git and the
single output lease. Administrative checks concern only lease, dependencies,
links and text integrity; they are not mathematical review.

Failure conditions for the conditional theorem include nonparametric source
rules, an adapter/conversion changing entry, independently chosen witnesses,
capture root replacement, missing P applicability, untyped imported values,
or resumed execution with different live-state/authority assumptions. Opaque
imports, arbitrary adapters, mutation, exhaustive Option 2 interpretation,
all-source admission, effective finite presentation, source principality and
`D_checked subseteq D_actual` remain unverified. No source rejection follows.

Recommended next action: construct the independent two-hole/environment and
whole-inlet typing clause for this P-generated root and prove its soundness
and completeness against the approved broad context domain, before using
the exact reached-cut relation or history induction to claim A.

## Commit packet

- Exact leased path:
  `notes/progress/2026-10-06-admission-A-exact-candidate-attempt.md`.
- Baseline SHA: `b0dd026bb9438b7dfb13c68a474a49145eb97555`.
- Dependency changes: none in the seven governing source dependencies or the
  twelve approved bundle files checked against baseline. Source-call target
  hash: `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073`;
  source-call review hash:
  `237b99131476e9f7876c3b3d52d05cae3613483d0b46e9be51dd3a2c54616417`.
- Review status: frozen unreviewed research; producer claims no independent
  certification. Conditional exact-cut result; A and production gates open.
- Checks already run: pinned governing-section inspection and direct
  dependency/approved-bundle equality. No tests/builds/experiments.
- Proposed checkpoint message:
  `Record exact captured-step admission cuts and remaining hole premise`.
- Shared-record deltas left for primary/curator: distinguish external step
  carrier from its inner returning Name carrier; preserve the reached-cut
  theorem as conditional; record `OpenInit`/whole-inlet interpretation after P
  as the residual A premise. No task/index/theory/question file was changed;
  no gate promotion is requested.
