# Source profile and initial admission: bounded premise falsification

Date: 2026-10-06
Baseline: `393b77b64cef03e74b3f1e76adb22c2aac5c981d`
Status: independently compiler-referee-reviewed bounded research checkpoint
Claim class: exact rule-premise inversion; finite logical discriminator
Scope: upstream inputs to the reviewed selected-source SV theorem
Authority / implementation authority: none
Exclusive lease: this note only

## Objective and result

Test whether the selected source's slot/Call registration, typed-core skeleton,
callback invocation law, or conditional C-realization already constructs a
compatible complete original profile and an independently admitted typed
invocation. The selected source remains

```text
my apply f = { my step x = f x; step }
```

The result is an exact inversion of the supplied rules: their constructive
conclusions do not remove those upstream hypotheses. The finite discriminator
below additionally separates local profile compatibility from independent
initial admission without making the conditional SV theorem vacuous. It is
not a Yulang source counterexample or a competing language interpretation.
No conclusion of semantic underspecification follows.

The distinct method here is premise/quantifier inversion with a nonempty
relational parameter discriminator. It does not reconstruct SV, run Frozen
Oracle, or repeat its returned-function path discriminator. The already
reviewed source-call note locates P/A cuts; this note tests the precise stronger
inference that local compatibility plus the conditional theorem supplies A.

## Baseline and governing clauses

All reads below matched the pinned revision byte-for-byte. SHA-256 hashes:

| Input | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-06-directional-source-view-instantiation-construction.md` | `462d792e518409199f77bb20a41aaa54d64898fe30363f98f0afff7ab3f805e3` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `tasks/current.md` | `df4c4915c0934fe65df658e3992ad4c26ed2598c5e99ffbe4749372f3c4789a1` |
| `notes/design/INDEX.md` (locator only) | `222eb6613c51e175de81be32172017e4f5fddcac18119716bdf675f841f3bbd2` |

Exact governing sections: inferred-call-views §§1.1–5; callback-delivery §§4–5;
source-contracts §§2–3.6 and §9; typed-core §§6–7; nested-block addendum §§2–4;
directional addendum §§1–4; reviewed SV §§3–6 and completeness limits. The
source-call construction §§4–7 supplies the already reviewed static versus
decorated distinction, not a new authority. Active rules
`research-lab.md`, `design-authority.md`, and `git-concurrency.md` were read.

Accepted decisions remain fixed: the upper output receives the selected
protection; the provider lower receives no backflow from it; actual role and
entry remain unchanged; `xi=(nu,K,D)` and original scopes are shared. The
block returns its captured local closure. Annotation absence is not an empty
effect claim. Production implementation and historical Oracle are not semantic
oracles for this argument.

## 1. Exact hypotheses and quantifier order

Abbreviate the following existing judgments for this proof audit only:

```text
S(C)           = selected resolved source and generated slot/upper schemas
P(C,xi,Gamma)  = one compatible complete original profile containing delta
I(C,xi,Gamma,t)= independently typed, initially admitted original invocation
H(I)           = its independently admitted finite prefixes, responses,
                 original raw resumptions, and reached future provider uses
```

These abbreviations are not proposed source predicates or implementation
atoms. The reviewed SV theorem has the following logical shape:

```text
forall C,xi,Gamma,t.
  S(C) & P(C,xi,Gamma) & I(C,xi,Gamma,t)
  => paired decoration/erasure/extension of every h in H(I),
     on that same Gamma,xi and original receiver.
```

Actual Return/rebind is an additional guard for rebound SourceViewInst;
actual Lambda/Name transitions guard capture/read. Receipt supplies Pending
evidence even if no Return occurs. Those established conclusions are retained.

Static totality has the different shape

```text
forall selected resolved C. exists generated dependent schemas S(C).
```

It does not assert `exists Gamma,t. P & I`. Likewise C-realization asserts a
correspondence **given** independently interpreted primitives, descriptor
typing, complete emission and admission certificates. Its admission induction
translates a supplied initial derivation and its extensions; it does not
manufacture the initial derivation from the existence of an emitted graph.

The coverage target must quantify over the independently specified original
source domain, rather than all raw syntax or all endpoint assignments. For
each eligible original invocation row it needs one full profile and one
typed/admitted original row, with its complete history relation. A separate
nonemptiness obligation applies only where the chosen source/context envelope
requires an admitted invocation. No claim here makes every raw argument legal.

## 2. Rule inversion

| Attempted supplier | What its premises/conclusion actually supply | Hypothesis still required |
| --- | --- | --- |
| Nested-block §§2–4 | Exact Lambda/Bind/Result/Call structure and lexical capture identity | Typed call view and capture/evidence transport; no source acceptance theorem |
| Inferred-call-views §2 | Selected shared formation direction, stable slot and source-owned relations; Q independence | Exact exhaustive formation judgments; §5 expressly requires profile and admission proof work |
| Typed-core §6 | Finite result/entry skeleton relative to lexical/declaration interfaces and typing premises | Satisfaction of complete invocation constraints, admitted annotations, recursive environment discharge |
| Generated Call | Dependent complete Function variable, upper occurrence and interpreted constraints | A satisfying witness and original-source interpretation of its complete profile/admission predicates |
| Callback §4 | Slot invocation view preserving actual role/entry | Concrete compatibility, typed receipt/Flow, Observe and complete-domain clauses on one fiber |
| Source-contracts §3.5 | Source-base membership/admission correspondence | §2 interpretation, descriptor typing and §§3.1–3.4 conformance, including independent initial admission |
| Reviewed SV §4 | Receipt-Upper and Pending/result/capture/read transport | Already independently typed actual invocation and compatible Gamma_original |

The generated Call relation is existential **inside** the original scope:

```text
exists_sigma F,e.
  WF_Dec(F;xi) & VIncl(A_f,F;xi,e_value)
  & WholeArgCompatible(J_x,CarrierContract(F);xi,e_arg)
  & CIncl(ExecuteCallableImage(...),Comp(E_c,A_c);xi,e_result)
  & TypedCallCert_Dec(c,F,e;xi) & generated source records.
```

Rule inversion of a satisfying decorated Call extracts this witness; emitting
this formula does not prove it true. `TypedCallCert_Dec` retains supplied
profile/receipt/observation premises. Nor does a witness to this local formula
alone establish that a candidate surrounding context is independently source
typed. The source-call note explicitly permits the relation to be empty.

Consequently, using C-realization as the missing supplier either leaves its
initial-admission and typing hypotheses unproved or assumes the sought result
inside its conformance certificate. Using callback §4 supplies the view law,
as the reviewed SV construction already does, while retaining that law's typed
invocation/domain premises. This is an exact premise classification within
the named inventory, not a proof that every possible source calculus lacks a
supplier.

## 3. Minimized nonvacuous discriminator

This finite relation is an **invented candidate parameter interpretation** of
the extracted implication, not a model of all approved Yulang source rules.
It specifically attacks:

```text
generated schemas + locally compatible complete profile + conditional SV
=> this candidate initial source context is admitted.
```

Use one source component, one original slot beta, one upper occurrence p0,
one complete candidate profile Gamma containing delta, one fixed xi, and two
candidate context/carrier tuples `a,b`. Preserve all static data and actual
entry/role. Supply the same local descriptor/Call compatibility predicates for
both tuples. There are no effects, captures or lower-profile mutations needed.

| Relation parameter | Model M0 | Model M1 |
| --- | --- | --- |
| Static generated schemas | Same S | Same S |
| Compatible complete profiles | `{Gamma}` | `{Gamma}` |
| Local decorated compatibility | `{a,b}` | `{a,b}` |
| Independently typed initial context basis | `{a}` | `{a,b}` |
| Admitted original invocation rows | `{a}` | `{a,b}` |
| Each admitted row's histories | Receipt followed by its typed Return/rebind | Same |

Interpret the source-base and emitted admission relations using the same
initial basis in each model; use identical constructor images for every
admitted row. Their conditional C-realization correspondences hold. Their
conditional SV lifting holds, nonvacuously on `a` in both models and on `b`
in M1. The local compatible profile and static data do not decide admission
of `b`: M0 excludes it through the unsupplied initial context parameter.

The changed relation is independent initial context typing/admission, not a
test of pending Q. No transition asserts that a typed Return makes its initial
context admitted. M0 is not an authorized rejection policy for Yulang. To
instantiate it as a source counterexample would require an approved source
derivation proving that the original source/context premises demand `b`;
none is supplied here.

Minimality is relative to this nonvacuous discriminator: one tuple cannot
both keep an admitted SV application and provide a different locally compatible
candidate whose admission differs. Two tuples and one profile suffice. No
claim of absolute logical-model minimality is made.

For the remaining full-profile cut, exact Call inversion is sufficient:
the conjunction above can be emitted without a witness. This note does not
invent a second latent position, a conflicting complete source profile, or a
new typed rejection example to make that existential fail. Those would need
the very original profile interpretation being investigated.

## 4. Complete histories and uniformity

Once Initial and typed extension predicates are independently supplied,
source-contracts §3.3 and the reviewed SV proof cover each admitted finite
history, including divergence, suspension and repeated raw resumption.
This theorem does not choose Initial, operation responses or future-use
eligibility. The Return-only discriminator above suffices for the initial
admission implication; it does not characterize those further predicates.

Any proposed upstream proof must retain the order

```text
one original xi and one compatible Gamma for the whole original invocation
then every admitted finite history and response/resumption extension.
```

Replacing it by `forall h. exists Gamma_h,xi_h` permits incompatible witnesses.
Even `forall h. exists Gamma_h` at fixed xi is not the required uniformity.
No finite-history enumeration or supplied-step checker alone proves either
the original history grammar or this uniformity. The reviewed SV proof retains
the original history relation; it already proves its conditional extension
and erasure, so that transport is not a reopened gate.

## 5. Independence, coverage, limits and verification

Oracle independence: no Oracle facts, execution, compatibility results or
production acceptance were used. The source authority comes from the pinned
documents. The relational discriminator shares static schemas, descriptor
compatibility and constructor images across its two models; its sole changed
parameter is the independent initial typed context basis. Because that basis
is not constructed, the discriminator cannot certify source semantics.

Coverage: hand derivation of exactly two finite models, one shared profile,
two candidate contexts, one fixed xi; no seed, random range or unbounded search.
Mutation: change only admission of `b` by changing the initial typed basis.
Failure condition: a constructive governing source rule whose already proved
premises force `b` into that basis defeats this independence model for that
source instance. Such a rule also supplies the next required evidence.

Commands/checks: narrow `cat`, `sed`, `rg` reads; `git rev-parse HEAD` and
read-only status; Python standard-library SHA-256 and `git show BASE:path`
byte equality for the ten listed inputs. All ten matched the pinned baseline.
Initial combined output was truncated; decisive source-contract, core, SV and
source-call sections were reread narrowly. No absence argument uses a truncated
capture. Final note whitespace and dependency revalidation are recorded in the
producer report. No builds, tests, executable semantic probe, Oracle run,
child, question or Git mutation.

Resource usage: sequential lightweight read/hash processes only; CPU/RSS and
exact wall time unmeasured. No search budget or coverage claim beyond the two
hand models. Only this leased note changed. Source acceptance, complete
profile construction, all-world admission, recursive environment discharge,
all-view principality and production Option A/2 containment remain unverified.

Recommended next action: construct the independent typed initial-context rule
for the selected source under one P-supplied complete original profile,
including caller/provider holes and the whole carrier at fixed xi; prove its
coverage against the original source context domain. Reusing SV or increasing
finite transition-model cases leaves this exact premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-source-profile-admission-falsification.md`.
- Baseline: `393b77b64cef03e74b3f1e76adb22c2aac5c981d`.
- Dependency hashes changed: none by this producer; direct inputs listed above.
- Review status: frozen unreviewed research; no independent-review claim.
- Checks already run: governing-rule inversion, two hand relation models,
  ten baseline/live input byte comparisons, dependency SHA-256 inventory;
  final whitespace/dependency checks reported separately.
- Proposed checkpoint message: `research: isolate original profile and initial admission premises`.
- Shared-record deltas intentionally left for primary/curator: record the
  nonvacuous local-compatibility/admission discriminator and exact initial-rule
  proof obligation; retain conditional SV closure and existing P/A status.
  No task/index/theory/authority files or question bundles changed.

## Independent review

A compiler referee reviewed the frozen artifact at SHA-256
`36dfaaf81c6d2831f8c93d50dd6cea8742869cdbaed8ea7f796aab3a0cf32fdd` and its
listed direct inputs; no blocking, major or minor finding remained within
scope. The review confirms only the bounded logical discriminator: local
profile compatibility does not itself entail independent initial admission.
The candidate parameter models are not a Yulang source counterexample, and
the note does not establish source underspecification or refute the
source-contract admission hypotheses.
