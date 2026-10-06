# Original association: conditional receiver-to-Call coverage lifting

Date: 2026-10-07
Baseline: `5ab30adc94d9fd70aad37525fc0f73d4ff024833`
Status: frozen research-only conditional derivation; compiler-referee review passed
Method: parameterized coverage lifting and scoped existential proof attempt
Exclusive lease: this note only
Claim class: conditional theorem and exact open introduction demand
Semantic/implementation authority: none

## 1. Objective and result

Attempt original source owner/view-kernel association for the five-node core
subtree of the approved source:

```text
my apply f = { my step x = f x; step }

call(result(name d_f), result(name d_x))
```

For every already existing original slot/contribution witness with an
independent complete receiver-coverage certificate, the source Return/Bind
equation lifts that coverage to this exact complete Call. The construction
retains all such witnesses and the original source/view coordinates.
It does not introduce a slot or contribution witness.

The missing step is a jointly sorted original introduction of static slot
ownership and complete receiver-contribution typing on the same `X/xi`.
`CALL_TYPE`, `SIG_RULES`, and `ORIGINAL_ASSOC` remain open. No attachment,
licensing, admitted-row existence, source adequacy, or production gate closes.

The earlier [constructor attempt](2026-10-07-original-association-constructor-derivation-attempt.md)
eliminates possible last rules. This note instead parameterizes over an
arbitrary existing original contribution contract, proves the coverage lift,
then attempts scoped existential introduction. The earlier
[dependent-fiber audit](2026-10-07-successor-source-association-falsification.md)
already identifies the event-free Name prefix; this note makes explicit the
conditional all-witness coverage theorem and its proof boundary. It claims
neither a new source counterexample nor independent review of those artifacts.

## 2. Governing sections and explicit hypotheses

Authority and exact scope:

- [FVIEW](../design/2026-10-05-inferred-function-call-views.md) §§1–5 and
  approved [function-call-view-formation/q1/a2](../../questions/2026-10-05-function-call-view-formation/approved-answer.md):
  shared source formation, distinct annotation/public/internal layers,
  comparison independence, and explicitly open constructing judgments.
- [Callback-context delivery](../design/2026-10-03-callback-context-delivery.md)
  §§1–2: bounded known callback-context delivery; callback-literal B is retained.
- [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–3: exact sequential local binding, inert final return, and same outer
  `f` capture. This supplies no new call-view registration rule.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §3.1: decorated immutable envelope; §6.1: coverage retains the original
  non-coverage kernel. §§2.1–2.2 and §3.2 supply the independent interpretation
  boundary and complete Call/Return/Bind relation used below.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §6: source result-role construction; §9: complete invocation, carrier entry,
  pending suffixes and directions. §3 supplies the structural translation.
- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§2–4: original upper-output direction, separate provider provenance and
  retained source witnesses. Its formal notation remains Draft.
- [DAG](../theory/successor-proof-obligations.md), `CALL_TYPE`, `SIG_RULES`,
  `ORIGINAL_ASSOC`: required source/kernel association and independent complete
  typing remain open. The DAG is research navigation, not semantic authority.

Fix the original judgment context `Delta_X`: one whole candidate `X`,
`xi=(nu,K,D)`, original binder tree, providers, environment, current
configuration, continuation and source/view operands. No satisfiable or
admitted `X` is inferred from generation.

Separate the hypotheses:

`H_shape`: approved core correspondence, lexical resolutions `d_f,d_x,d_step`,
registered shared root `R_f`, ordinary source interfaces, and independently
justified unannotated seed/upper-exposure witness.

`H_exec`: independent original Name, Return, Bind and complete actual-provider
invocation meanings; the original typed metadata required to interpret those
relations; compatible current-state and source/view coordinates. This does
not include an original association of this Call with `(s,c)`.

`H_type`: if invoked, the independent pointwise `CALL_TYPE` theorem under
fixed ordinary descriptor/carrier/admission meanings, without attachment in
its premises. This is a conditional input; the current DAG marks it open.
The coverage lemma below does not prove or require completion of that gate.

`H_cover(c,w)`: an independently interpreted original complete contribution
contract and its coverage of the complete receiver family at the original
incidence. This is a supplied conditional certificate, not a source rule
derived here or a definition of contribution membership as a source image.

`H_assoc`: original source-owned slot/contribution introduction, the target
premise. It belongs to none of the hypothesis sets above.

## 3. Source construction and complete receiver family

At the original body scope `sigma_x`, typed-core §6 gives:

```text
Gamma(d_f)=Value(A_f)       Gamma(d_x)=Value(A_x)
n_f=result(name d_f)        n_x=result(name d_x)
I_fx=Computation(E_fx,A_fx)

ell  = original f x Call occurrence
beta = (d_f,R_f)
p0   = outEff(U)
e0   = (k,beta,u,sigma_x,p0)
```

`U`, the Call endpoints and their constraints remain symbolic. Source parameter
Value tags do not select the actual incoming callable's role or entry.
The outer block constructs and returns the capturing `step` closure without
executing this body. Actual outer/inner entry transitions are required before
their rebound Name computations can be read.

Under `H_exec`, construct:

```text
J_f = ReturnImage(Name(d_f), original environment)
J_x = ReturnImage(Name(d_x), original environment)
T_x = Delay(J_x, original lexical references)

j_call = J_f >>= (actual_f ->
           ExecuteCallable_X(actual_f,T_x; original U/view operands))
```

`J_x` reads the inner rebound `x`. It is not the external carrier that entered
`step`. The delay contains code and original lexical references; it does not
freeze a prior configuration. If executed after resumption it uses the current
state according to the original primitive relation. Returning a latent value
does not recursively force it.

The receiver family retains every actual component:

1. Actual receiver activation, source boundaries and receipt.
2. Value entry's one designated argument execution and typed result rebind;
   or retained entry's binding of the same carrier without that entry Force.
3. Actual provider body and its independently designated consumers.
4. Designated result consumer, native return delimiters and invocation return.
   An operation keeps its declaration-derived result consumer after native
   return within the complete consumer view.
5. Every pending continuation/suffix, original operation/response/provider
   coordinates, and current resumed state, without receipt replay.

Actual provider branches remain separate from the formal's provisional
protected Handler view or later formal-use refinement. Ambient handlers are
the independently source-typed original contexts allowed by §3.1. Their
selection is not reconstructed by this proof. Source-contracts §3.1 excludes
implicit adapters; this note supplies no adapter case.

## 4. Conditional lifting, parameterized over every original witness

At the actual Name read, `H_exec` supplies

```text
J_f(C)=Return(f_star,C).
Return(f_star,C) >>= S = S(f_star,C).
```

Let `F_call(X)` be the complete relational interpretation of `j_call` and
`F_recv(X)` the interpretation of its receiver suffix after that returning
prefix. Both are considered inside the unchanged original source record
`ell`, view operands and metadata. The Return/Bind equation gives

```text
F_call(X) = F_recv(X).
```

This is equality of complete computation relations under `H_exec`, not
equality of static signature slots, contribution indices, proofs or source
syntax. The callee-read provenance stays in the original Call record. This
proof performs no source rewrite and asserts no kernel congruence under
arbitrary rewrites. A computed-callee request would invalidate this equality.

Fix any existing `(t,w) in I_orig(X)`, with

```text
t=(beta,s,p0,c)
s : original static signature slot
c : original complete contribution contract/witness.
```

For this proof only, `Cover_X(c,w;F)` denotes the query that every complete
output/pending observation and its dependencies in `F`, at the unchanged
source/view incidence, satisfies the independently interpreted contract for
this original `c,w`. All original local witness scopes are retained. This
notation does not define an adopted Yulang predicate or reinterpret
`I_orig`. The contribution may conservatively allow additional observations.

**Conditional coverage-lifting lemma.** For every existing original witness,

```text
H_shape, H_exec,
(t,w) in I_orig(X), Cover_X(c,w;F_recv(X))
----------------------------------------------------
Cover_X(c,w;F_call(X)).
```

Proof: take any complete observation with its original dependencies in
`F_call(X)`. The same observation/dependencies belong to `F_recv(X)` by the
Return/Bind equation. Apply the supplied coverage certificate at those same
coordinates. For a request the existing bind equation retains

```text
Request(q,C,k) >>= S
  = Request(q,C, lambda(response,C'). k(response,C') >>= S).
```

Thus the equality retains suspension and the unfinished entry/body/consumer/
return suffix; the argument does not restrict itself to returning executions.
Future uses and raw resumptions, to the extent present in the independently
interpreted complete relation, keep the same original admission and witness
tree. No initial-world or history-domain existence follows.

The lemma is universal over existing witnesses. It neither chooses a
representative nor removes other legitimate witnesses. It proves coverage
conditional on `H_cover`, without manufacturing membership in `I_orig(X)`.
It is not a theorem validating the independent source/contract premises.

## 5. Scoped existential introduction attempt and exact stop point

The constructive target is a jointly sorted introduction, at the original
permitted binder position:

```text
Delta_X ; original own-upper source arm (d_f,R_f,u,sigma_x,ell)
        ; independent complete invocation typing
  |- Sigma_(t,w in I_orig(X)).
       OriginalSlotOwner(w; beta,s,p0,d_f,R_f,u,sigma_x)
     x OriginalContributionTyping(w; c,f_star,T_x,U,ell)
```

These names express missing proof obligations, not adopted semantic
definitions. The second certificate must include independently justified
complete receiver coverage for the original contribution contract; ordinary
`Comp(E,A)` typing is not a sort conversion to that contract. It must retain
actual stage/view incidence and own-upper versus inherited-provider/result
arms. The coverage lemma then supplies the complete `j_call` side.

The Sigma remains under the original `Delta_X` binder tree. Event/history-local
witnesses remain below their original rigid dependencies. A static slot and
complete contribution certificate cannot be replaced by independently chosen
per-observation marginal witnesses. No original quantifier is commuted here.
The desired output includes every legitimate original witness; it stipulates
neither `s=p0`, `c=j_call`, nor a singleton slot inventory.

This introduction cannot be discharged from the supplied premises. Even
conditionally adding `H_type` yields ordinary output/pending descriptor typing,
without an original `s,c,w` introduction. Source-contracts §6.1 adds allowances
while retaining the non-coverage kernel. Callback B consumes a known callback
contract; it does not form this unknown `f`'s original kernel. The local `step`
literal is not supplied with such an expected callback context here.

The precise openness is recorded in FVIEW §2 (constructing judgments remain
open), §5 (source/profile/owner generation required), and approved q1/a2
(formation direction selected; detailed rules/proofs not completed). The
nested addendum §3 provides no call-view registration rule. Independently
supplied owner/view contracts in source-contracts §§2.1–3.1 cannot be projected
as a newly derived source association if they already contain this target.

This is a failed constructive introduction with a conditional coverage lemma,
not a whole-repository nonderivability theorem or a demand for a new language
meaning. The five-node subtree is the previously established proof cut; no new
minimized source counterexample is claimed. The original `CALL_TYPE`,
`SIG_RULES`, `ORIGINAL_ASSOC`, attachment and licensing gates remain open.

## 6. Independence, checks, failures and omissions

There is no Oracle, executable reference, checker, seed/range, enumeration or
executed mutation. This derivation shares its independently supplied execution,
admission, metadata and contract premises. A checker assuming the missing
joint introduction would establish rule-relative consistency, not prove those
source rules. This producer has not independently reviewed its output.

Failure conditions include an effectful computed callee, invalid original Name
lookup, loss of original source/view metadata, body-only coverage, substitution
of the external `step` argument carrier for `J_x`, provider retagging, repeated
receipt on resume, or witness movement across original scopes. Coverage of an
empty family does not establish an original incidence or admitted row.

The earlier attempts leave the same introduction premise untouched. This note
stops after deriving the conditional lift and isolating that premise; another
packet replay or larger transition search would not discharge it.

Recommended next action: pin an independently justified original kernel
introduction with the jointly sorted output in §5, then derive its exact
own-upper Call arm, before another attachment or licensing proof.

Commands already run: read-only `git rev-parse HEAD`; bounded `git show
<baseline>:<path>` and section reads; navigation `rg`; Python byte/SHA-256
comparisons for the seventeen direct inputs below. Initial combined captures
truncated; decisive clauses were reread narrowly. Before writing, all inputs
matched the baseline and the leased output was absent. Final integrity checks
and dependency recheck are reported in the accompanying commit packet.

One leased note; no compiler, cfg(test), shared task/index/authority or question
bundle edits. No Git mutations, builds, tests, formatting, children or heavy
processes. Earlier independent read batches used at most four lightweight
commands; final hash comparisons were sequential within one Python process.
No numerical CPU/RAM/wall-time ceiling was supplied. CPU time, peak RSS and
elapsed wall time were not instrumented.

Unverified: independent complete contribution interpretation/introduction,
`CALL_TYPE`, complete original signature/licensing rules, admitted original
row/profile existence, generalized/annotated/recursive and computed-callee
cases, all-world admission, source adequacy, principality, production membership
and cutover. Nothing here modifies their scope or selects a rejection policy.

## 7. Pinned direct dependencies

SHA-256 values below are the baseline bytes; none changed before writing.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md` | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| `notes/progress/2026-10-07-original-association-constructor-derivation-attempt.md` | `bfd197a094a6fa3e813325a40c361687ed609ad45aa89af9908f58ce240b5435` |
| `notes/progress/2026-10-07-original-association-inversion-attack.md` | `c8aa0c87d078cdc2d1976bbe00e925f33177c761ae9cb196ce3d3ae79cf84a83` |
| `notes/progress/2026-10-07-original-association-source-kernel-audit.md` | `509e9af6be0ae3b3560f1fd7ca8e9c06572bb65e1351b114b0e2e5e13061b202` |
| `notes/progress/2026-10-06-attach-call-contribution-construction.md` | `4261105c8f9a5012a693cc39dc0f7df8c0e70024594a10282046dbaebf851a96` |
| `notes/progress/2026-10-06-attach-law-construction-attempt.md` | `b94e829e06027c2bd4cc2f0dbf4a33dc954aa10ee058fbc4918da75ad151a241` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-original-association-conditional-call-lift.md`.
- Baseline SHA: `5ab30adc94d9fd70aad37525fc0f73d4ff024833`.
- Changed dependency hashes: none; seventeen direct inputs matched before writing.
- Claim/review status: compiler-referee-reviewed conditional research derivation;
  no semantic authority or closed gate.
- Checks already run: pinned governing/prior-note reads; seventeen dependency
  byte/hash comparisons; leased-path absence. Final path-local integrity and
  freeze hash are supplied in the handoff report.
- Proposed one-line commit message: `research: record conditional original Call coverage lifting`.
- Shared-record deltas intentionally left for primary/curator: optionally cite
  the conditional lift and exact joint introduction demand; keep `CALL_TYPE`,
  `SIG_RULES`, `ORIGINAL_ASSOC` and downstream licensing open. No shared record
  or question bundle changed.

An independent compiler-referee review passed with no findings. It confirmed
that the Return/Bind equation lifts a supplied complete receiver-coverage
certificate without introducing an original slot/contribution witness, and
that the displayed joint Sigma remains the exact missing premise. The review
checked the seventeen cited dependencies against current bytes. It did not
close `CALL_TYPE`, `SIG_RULES`, `ORIGINAL_ASSOC`, original contribution
interpretation, admission/inhabitance, licensing, principality, production
conformance or generalized cases.
