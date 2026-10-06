# Captured-step extra-origin search: the argument-side contract cut

Date: 2026-10-06
Baseline: `c8a673342b5697db11427dfdb8204da1c075cf74`
Status: frozen research-only bounded characterization; independent review pending
Method: manual source-rule attribution, one exact tree, no checker
Exclusive lease: this file only
Semantic / implementation authority: none

## 1. Objective and result

Try to refute `Applicable_original(C,d_f,R_f,p;xi) => p=p0` with an
independently licensed source origin for the exact selected source:

```text
my apply f = { my step x = f x; step }
```

No source-valid extra-origin witness follows from the inspected rule basis.
This is a bounded unsuccessful search, not absence of extra origins globally
and not a singleton theorem. The original applicability relation still lacks
its complete independently interpreted source introduction rules.

The previous investigations already tried dependent result profiles, implicit
formal introduction, administrative Force counting, dynamic boundaries and
candidate-grammar inversion. This pass examines the **argument side** of the
same original Call. In particular, `J_x` returns an ordinary value, but that
value may have latent callable paths. Neither an empty immediate argument
effect nor ordinary Value evidence supplies a negative theorem about original
profile positions at those paths. Conversely, a profile received with `x`
does not become an original introduction by this component at `beta_f`.

The resulting refinement is small: existing `I-call-rest` must cover any
parameter-side original contract schemas as well as result-side schemas. It
is not a new gate or evidence that either kind is licensed. A result-only
negative lemma would leave this part of the singleton obligation unproved.

## 2. Authority and retained dependencies

Authority is [inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, the integrated [q1/a2 answer](../../questions/2026-10-05-function-call-view-formation/approved-answer.md)
and [receipt](../../questions/2026-10-05-function-call-view-formation/receipt.md),
and the [nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–4. These fix sequential binding, returning `step` without calling it,
resolution to the same outer `f`, lexical capture, one shared inferred
contract, stable source identity/scope, and admission independent of Q.
Annotation absence causes full protection at applicable positions; ordinary
Value evidence refines the same provisional formal/use relation without
rewriting an actual supplied callable's role or entry. Source annotations,
public types and internal evidence remain distinct. No alternative source
meaning is selected here.

Conditional rule inputs are [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3/10, [typed-core](../design/2026-10-02-typed-computation-core-elaboration.md)
§6 and [typed-boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§6. They preserve supplied typed/profile data; their execution and transport
inventories are not raw-source profile introduction inventories.

Prior research read at the pinned baseline:
[origin construction](2026-10-06-profile-origin-candidate-rule.md),
[origin premise attack](2026-10-06-profile-origin-rule-candidate-attack.md),
[extra-origin classification](2026-10-06-profile-extra-origin-falsification.md),
[formation interface](2026-10-06-formal-profile-formation-rule-attempt.md),
[original introduction attempt](2026-10-06-profile-original-introduction-construction.md),
[source normal form](2026-10-06-profile-source-normal-form-construction.md),
and [Call construction](2026-10-06-source-call-generation-construction.md).
Their positive immediate seed is retained. Their failed routes are not rerun.
The [Oracle crosswalk](2026-10-06-main-source-generation-oracle-crosswalk.md)
was read for its authority boundary; no historical rule, algorithm, marker,
trace or acceptance result chooses a candidate or supplies a premise below.

Explicit hypotheses:

- **Hsource, established selected meaning:** the exact resolved tree and
  source annotation absence, with original `d_f,d_x,c` identities and scopes.
- **Hseed, retained bounded research result:** the Call construction produces
  shared `R_f,F_c,beta_f=(d_f,R_f)`, immediate `p0=(beta_f,call.effect)` and
  `ElimOrigin(c,...)`. It does not supply complete original applicability.
- **Harg, conditional source-rule basis:** typed-core §6 supplies the ordinary
  parameter/Name/Result skeleton and whole-argument Call constraint.
- **Himage, conditional typed realization:** any discussed argument transport
  uses an independently typed correspondence and retained original witnesses;
  `chi,D` move by indexed image, and `K,L` remain attached under one `xi`.
- **Horigin, search criterion:** a witness must be an introduction by this
  original component at this formal root, rather than an incoming fact with
  an equal static beta label. A proposed dependent schema needs its original
  source rule before instantiation.

No exhaustive introduction grammar, completed admission relation, typechecked
source realization or original-solution lifting premise is assumed.

## 3. Argument-side derivation and candidate sites

The selected subtree and ordinary source interfaces are:

```text
c = call(result(name f), result(name x))
Gamma(f)=Value(A_f)                Gamma(x)=Value(A_x)
J_x=ReturnImage(Name(d_x), original environment)
Result(Value(A_x))=Comp(empty,A_x)
```

By typed-core §6, constructing `result(name x)` returns the already rebound
value. Substitution assigning a Function or computation-data shape to `A_x`
does not introduce another Force or Call. The source rule then relates this
**whole** `J_x` to `F_c`'s parameter interface. It does not choose that
interface, the supplied callable's entry, or an original parameter profile
by inspecting the printed empty effect row.

These are argument-side coordinates, not additional source programs:

| Candidate site | Source-rule consequence | Extra-origin status |
| --- | --- | --- |
| Effect exposure of the inner carrier `J_x` | It is Name-return of the already rebound value; its construction does not execute a latent component. Effects of the external carrier supplied to `step` belong to step's earlier entry. | An entry event or a zero immediate row does not determine a new original position of `beta_f`. A separate parameter observation position would first need its independently interpreted descriptor and source origin. |
| A latent callable/computation path of `A_x` | The Value tag permits such a shape and its supplied packet can retain matching latent profiles. No recursive Force follows. | Incoming latent evidence remains inherited. A new `beta_f` parameter-path schema is unlicensed without a formal/Call introduction rule. |
| A callee-parameter contract used at argument checking/receipt | The complete Call relates the whole argument to the parameter with existing typed-path/contract obligations. A lawful argument correspondence can move supplied evidence. | Its original source profile is a premise, not a first-generation conclusion. This is the parameter part of `I-call-rest`, potentially coupled to `I-formal`. |
| Original contract of the local formal `x` | Ordinary syntax generates its Value interface and entry/rebind skeleton at `d_x`. Any original nested-profile producer for it remains unspecified. | `d_x` is not `d_f`. Turning an x-owned origin into a new f-owned original contract needs a genuine source incidence/introduction derivation; endpoint equality or contravariance alone cannot do it. |

The first row refines the prior external-entry distinction; the remaining
rows separate parameter-profile inputs from the previously emphasized
callee-result projection. These rows are not claimed to exhaust all lawful
source introductions or all latent parameter paths.

For an independently supplied input profile fact at latent path `q_x`, the
typed image has the form

```text
chi_received(q,b) iff exists q_x.
  chi_x(q_x,b) and M_arg(q_x,q).
```

Keep the original certificate for the chosen input fact. `M_arg` changes its
view position; it does not substitute `d_f` for its original owner or create
a first-introduction certificate. Even if its static beta label equals
`beta_f`, it can be an incoming view of another use/activation of that same
template. That fact is not a new introduction by C. With no such input fact,
this image arm supplies no output; a separately introduced parameter contract
would be a different source, whose first generation must be justified.

This is an application of the retained indexed-image rule to this argument
site, not an independent proof of that rule or of source completeness.
Any actual correspondence/receipt and source-typed initial admission still
need their own realization certificates.

## 4. Smallest attempted falsifier and precise blocked inference

The smallest schematic candidate keeps the single source Call, one ordinary
argument endpoint and one latent effect port. For illustration only, suppose
a joint assignment has

```text
nu(A_x)=Fun(Value(T),Comp(E,U))
q_x=call.effect of that latent argument value
```

This is a candidate assignment, not a proved satisfying typing for C. It
does not assert that `x` is invoked anywhere in C. If an independently typed
parameter correspondence places that latent port at a path `s_arg` of
`F_c`, the attempted extra position is `p_arg=(beta_f,s_arg)`, distinct from
the outer complete-invocation `p0`. The required conclusion is:

```text
resolved C,d_f,d_x,c; original shared R_f,F_c,sigma,xi
NoAnnotation(d_f); ordinary J_x; independent parameter-path derivation
plus an independently licensed original formal/Call introduction
------------------------------------------------------------------
Intro_original(C,n,d_f,R_f,p_arg,kappa;xi), p_arg != p0
```

The final premise has no supplied rule deriving it from this source. A
preintroduced dependent schema could avoid origin creation from solved shape,
but naming `c`, `A_x` and `s_arg` in that schema does not license it. An
incoming `chi_x` certificate fills only the transport premise, not this
original-introduction premise. Source rules must also preserve the original
scope of all dependencies; moving an inner `A_x` witness into an outer-root
profile by independent existential choice is not a permitted shortcut.

This candidate is minimized as an **unproved rule obligation**: one source
application, one latent argument port and one proposed origin. Removing the
port eliminates the extra-position candidate; removing its origin removes
the alleged original applicability. It is not a minimized source-valid
counterexample or an execution/acceptance claim.

The key prospective falsifier is a source-derived formal/Call rule that
actually concludes this parameter-path origin at the same original joint
fiber, with independent admission and scoped contribution interpretation.
Such a rule would refute the singleton without adding another syntactic Call.
Conversely, excluding only dependent result origins would not prove singleton:
the original first-introduction inversion must account for parameter origins
too. The broad `I-call-rest` obligation already encompasses them; its
result-focused examples must not silently narrow the quantifier.

No candidate origin is promoted by annotation absence. Full protection is
policy at an applicable position, not a constructor of every descriptor path.
The provisional/refined role labels are likewise no original path oracle.
Production Option 2 extras concern membership observations and supply no
original profile introduction certificate here.

## 5. Independence, stopping point and limits

There is no executable oracle. The crosswalk contributes no semantic rule;
the candidate depends only on the selected source skeleton and current
typed-core/typed-boundary contracts. Shared assumptions with prior research
are Hseed and decorated transport. Thus this is not independent validation
of their source validity. A checker that adds this parameter schema, or omits
it by definition, would assume the very original source premise at issue.

Conceptual mutations checked by rule inspection: replace `J_x` by an arbitrary
carrier with the same printed interface; use empty immediate support to erase
latent evidence; relabel an x-owned origin by endpoint equality; attach a
dependent parameter schema before solving. The first three do not supply a
valid original introduction and can violate the source/packet premises. The
fourth preserves the no-solved-shape-origin discipline only if its missing
source introduction is independently justified. No mutation was executed.

The prior grammar and first-introduction attempts leave the same source
profile operand untouched. This pass identifies its parameter-side subcase
and stops. It does not propose another equivalent toy probe or claim that
the absence of a supplied rule proves an eventual rule impossible.

Coverage: one selected tree, four argument-site distinctions and one symbolic
single-latent-port attempt; no exhaustive enumeration of value shapes, typed
paths, source grammars, assignments, future clients or histories. Seeds and
numeric ranges are inapplicable. Omitted cases include arbitrary nested and
recursive parameter paths, coupled parameter/result origins, annotated or
multi-use variants, actual provider/capture/receipt/liveness, initial admission,
contribution normalization, all-original-solution lifting, soundness and
principality, B-equivalence and Option A/2 production conformance. No global
absence or gate closure follows.

Failure conditions: an already governing original parameter-origin rule in an
uninspected source defeats the no-witness report; a supplied conversion that
is actually first introduction defeats the assumed transport classification;
invalid path/scope certificates defeat the conditional argument derivation.
No complete search outside the assigned dependency set was attempted.

Commands/checks: read-only HEAD/status, bounded `rg` locators, pinned `git show`
section reads, Python standard-library dependency-byte/SHA-256 checks, and
leased-note metadata checks. Initial combined captures were truncated;
decisive governing and prior derivation sections were recovered narrowly.
No compiler/Oracle/test/build, Git mutation, child delegation or shared-file
write. Resource use was short lightweight read/check processes and one manual
note; zero heavy processes. No numeric CPU/RAM/wall-time budget was supplied;
CPU, peak RSS and reasoning wall time were not instrumented.

Recommended next action: obtain one independently interpreted original
formal/Call profile rule covering **both parameter and result dependent paths**,
then review its witness inversion and whole-xi source-solution preservation.
Retain P open until that rule supplies either the singleton converse or a
licensed extra origin.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-profile-extra-origin-falsifier-next.md`.
- Baseline SHA: `c8a673342b5697db11427dfdb8204da1c075cf74`.
- Dependency hash changes: none observed for the direct assigned inputs at
  the pinned-byte comparison; final recheck recorded in the submission report.
  All semantic reasoning uses baseline blobs, never unfinished concurrent edits.
- Review status: frozen producer-authored research-only characterization;
  independent review pending; no theorem, authority or implementation promotion.
- Checks already run: exact governing/prior source reads, argument-side manual
  derivation and conceptual mutations, direct dependency-byte/hash comparison,
  note whitespace/final-newline/local-link checks. No tests/builds requested or run.
- Proposed one-line research-checkpoint commit message:
  `research: isolate parameter-side original profile introduction obligation`.
- Shared-record deltas intentionally left for primary/curator: retain
  `I-formal/I-call-rest/I-exhaust` and P open; clarify that `I-call-rest` covers
  parameter as well as result schemas; record no licensed extra origin found
  in this bounded argument-side search. No task/index/theory/authority/question
  record was edited.
- Writes stop before frozen submission; primary owns review and integration.
