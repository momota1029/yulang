# CALL_TYPE: constructive local typing attempt

Date: 2026-10-07
Baseline: `035f7f8e97f5544ccd028bd1f167b83054134fdc`
Status: frozen research-only derivation attempt; compiler-referee review passed
Method: construct the ordinary typing proof through actual entry, then isolate its first unavailable semantic rule
Exclusive lease: this note only
Claim class: conditional operational reduction and bounded premise localization
Semantic/implementation authority: none

## 1. Objective and result

Attempt DAG `CALL_TYPE`, rather than `ORIGINAL_ASSOC`: ordinary descriptor
typing of every complete Call output and pending observation at each
independently admitted operand/world assignment on one original `X`.

The construction reaches an unavailable **carrier elimination consequence**
already in a Value-entry identity receiver. Its one argument Force must return
a value satisfying the independently interpreted parameter predicate, and a
suspended Force must satisfy the independent pending predicate with the
original rebind/body/consumer/return suffix. The operational entry equation
does not supply either implication.

The terminal reduction below is proved relative to the supplied ordinary
execution relations. The descriptor implication is not proved. This is a
smaller proof obligation than original slot/contribution introduction and
requires none of its witnesses. No claim of globally minimal axioms or
whole-repository nonderivability is made. `CALL_TYPE` remains open.

## 2. Baseline, governing sections and hypotheses

Exact inputs:

- DAG `CALL_REL`, `SEM_JOINT`, `CALL_TYPE`: the first is conditionally closed;
  the latter two remain open. The DAG locates obligations, not language meaning.
- Source contracts §§2–3: independent whole-tuple primitive/constructor
  relations; ordinary `DescMem` is independent of the source image. §2.2
  explicitly requires constructor typing, and §3.5 assumes local descriptor
  typing lemmas. §3.3 separates initial admission, responses, raw resumptions
  and future uses. §3.7 retains the approved Option 2 allowance for licensed
  production extras without a source witness.
- Source contracts §5: same-operand positive constructor congruence and
  guarantee-bound absorption; neither supplies ordinary constructor typing.
  §10 preserves missing concrete membership/admission and production gates.
- Typed core §9: whole carrier, actual provider-owned Value/retained entry,
  current-state resumption, declared result consumer, complete pending suffix
  and separate invocation versus body ports. §§2–3/6 are inspected only to
  instantiate the ordinary identity body and actual execution equation.
- Authoritative callback-context §§1–2.1: boundary before body, independently
  synthesized endpoints, completed ordinary inequality; preserve actual role
  and entry. The known callback context is not a local typing certificate.

The prior source-call construction imports `TypedCallCert_Dec` and a complete
`CIncl` premise. The association audit explicitly leaves constructor typing
open. The prior conditional Call lift proves transport of supplied receiver
coverage, not the local descriptor implication sought here. None is reused
as evidence that `CALL_TYPE` holds.

Fix `Delta = (X,xi,original binder tree,environment,providers,current world,
source/view operands)` with `xi=(nu,K,D)`. Quantification over Delta stays
outside observation-local witnesses, at the original scopes. It does not
assert that any independently admitted Delta is inhabited.

Separate hypotheses:

`H_rel`: the supplied ordinary Name/Return/Bind and actual provider execution
relations, including their original receipt, entry, consumer and native return
delimiters. These are the conditional `CALL_REL` premises.

`H_sem`: one fixed, independently justified `SEM_JOINT` interpretation of
descriptor, carrier, provider-entry, consumer, world and admission predicates.
This is a parameter, not a construction completed by this note. Its actual
clause specifications must be available to prove a local typing rule.

`H_operands(Delta)`: independently admitted Call operands/current world under
that interpretation, with the ordinary callable and whole carrier predicates
and their joint dependencies. Admission does not ask whether this Call or a
pending Function comparison succeeds.

No hypothesis includes `TypedCallCert`, `CIncl` of the sought complete image,
attachment, static signature ownership, original contribution coverage,
source-world existence or whole-source coverage.

## 3. Exact local target and constructive proof tree

Use proof notation, without defining the independent predicates:

```text
J = J_f >>= (f -> ExecuteCallable(f,Delay(J_x)))
T_Call(Delta,O) = the fixed ordinary DescMem predicate at this Call result
```

`O` includes the complete provider/observation/current-state tuple and pending
continuation when present. The target is

```text
forall Delta. H_sem(Delta) and H_operands(Delta) =>
  forall O. O in J(Delta) => T_Call(Delta,O).
```

The complete relational image and `T_Call` are distinct. Membership of `O` in
the former cannot define or certify the latter.

Expand the execution tree before attempting its descriptor proof:

1. Callee evaluation returns an actual callable, suspends with its invocation
   suffix, or contributes another specified finite prefix.
2. On its Return branch, construct the argument carrier inertly and establish
   the actual receiver's boundaries/receipt.
3. Value entry executes exactly one designated argument Force, then performs
   typed result rebind; retained entry binds the same carrier without that
   Force. Neither branch changes the actual callable's role.
4. Execute the actual body, designated result consumer and invocation return.
   An operation keeps its declaration-derived consumer after native return.
5. Each exposed Request retains the unfinished suffix and original operation,
   response/raw-handle coordinates. Resumption uses the current resumed state
   without repeating receipt.

The corresponding descriptor proof needs consequences of the independent
predicates at each step. Semantic activeness (§2.2) means a predicate is
conjoined; it does not prove these consequences. Positive congruence (§5.3)
transports an already proved relation inclusion with unchanged operands; it
does not introduce an inclusion into an independently interpreted descriptor.

## 4. Terminal identity reduction and first unavailable premise

Instantiate only the Value-entry closure with body `result(name z)`, at an
ordinary symbolic parameter endpoint `A`. Keep its actual role, receiver,
receipt, body environment and return delimiters. Let the supplied relations
contain the terminal Force branch

```text
Force(t,C_enter) = Return(a,C_after_force).
```

For this branch, the entry/Return/Bind equations derive

```text
Force(t) >>= (a -> Rebind(z,a); Return(lookup z); ReturnFromInvocation)
  = Rebind(z,a); Return(a); ReturnFromInvocation.
```

**Conditional terminal reduction.** For every fixed Delta, every `a` and
`C_after_force`, and every original shell witness `w` for this branch, the
receiver execution has the corresponding invocation-return observation
`O_ret(a,C_out,w)`, whenever the original rebind/body/return premises hold.
The returned value is the same `a`. The current configuration is the actual
`C_out` after the original return delimiters, not a substituted pre-entry
world. Proof: substitute the Force Return into ordinary Bind, apply the
actual rebind/Name equation, then the actual invocation-return relation.
No descriptor membership is used in this reduction.

The required leaf of the typing proof is consequently

```text
H_sem, H_operands(identity receiver,t,C_enter),
Force(t,C_enter)=Return(a,C_after_force), original shell witness w
------------------------------------------------------------------- missing
T_Call(Delta,O_ret(a,C_out,w)).
```

This is a precise terminal carrier/provider elimination consequence, rather
than an original association or a whole-source existence requirement. Even
when the ordinary return clause exposes value membership of `a` in `A`, one
must derive it from the **whole carrier's** independent membership/admission
clauses. `P=Value(A)` states what entry demands; typed-core §9 expressly says
it does not prove the incoming carrier pure. A formal syntactic environment
`z:Value(A)` does not validate the actual semantic value inserted by rebind.

For clarity, the further implication

```text
T_Call(Delta,O_ret(a,C_out,w)) => ValueMem(A,a,C_out; original dependencies)
```

is a candidate ordinary Return-inversion clause until supplied by the fixed
descriptor specification. This note does not silently adopt it. If that
clause is independently supplied, the local target necessarily implies the
displayed value-membership conclusion for every such Force branch. This
conditional necessary consequence exposes the exact interface between
carrier execution and ordinary value membership; it does not prove it.

The first missing rule is thus not an existential slot introduction. It is
the independently grounded implication from admitted whole-carrier behavior
through actual entry/rebind to this ordinary return predicate. The assigned
sources invoke the corresponding local typing lemmas instead of deriving
their semantic leaves. Naming it `TypedEntry` would leave the premise intact.

## 5. Pending obligation and incidence preservation

For the same receiver, the supplied Bind rule derives

```text
Force(t,C_enter) = Request(q,C_pending,k)

Request(q,C_pending,k) >>= S
  = Request(q,C_pending, (response,C') -> k(response,C') >>= S)

S = original rebind; identity body; designated consumer; invocation return.
```

The separate missing descriptor leaf types this pending observation with
`k >>= S`, at the same request/response/raw-handle and original dependencies.
Its continuation consequence ranges over every independently admitted
response/resumption at the current `C'`, rather than one returning sample.
The terminal leaf alone is insufficient for `CALL_TYPE`; divergent or other
finite prefixes additionally need their specified ordinary clauses. Those
clauses are not exhaustively supplied by the two displayed Bind equations.

A computed-callee Request precedes receipt and retains
`k_f >>= ExecuteCallable`; it has callee-prefix incidence. An argument-entry
Request occurs inside the actual receiver activation and retains the suffix
above; it has receiver-invocation incidence. `T_Call` must interpret each at
its own original incidence. No equation marks both as the receiver upper
output. For the exact `f x` Name prefix, the prefix is returning under the
supplied lookup premises; the receiver's pending typing obligation remains.

## 6. Falsifier, independence, coverage and stopping point

Smallest useful proof discriminator: the terminal branch in §4, with a typed
identity-provider premise, an independently admitted whole carrier, one Force
Return and its original shell witness. A fixed independent interpretation
that satisfies these premises but rejects `T_Call(O_ret)` falsifies the local
law on that interpretation. With an independently justified Return-inversion
clause, an argument value outside `ValueMem(A)` is the corresponding failure.
No such admitted-language witness is constructed here; these are exact
falsification conditions, not a new Yulang counterexample or permission to
choose arbitrary per-node predicates for `SEM_JOINT`.

This is a proof-construction attempt with universally quantified symbolic
operands. No bounded enumeration, seeds/ranges, random trials, executable
mutations, checker or Oracle is used. The terminal instantiation does not
establish complete observation coverage. The Request calculation is a
separate operational derivation whose typing remains open. Shared assumptions
are the original operational equations and independent predicate meanings;
there is no independent semantic oracle. A checker assuming the terminal and
pending typing rules would check consequences of those assumptions, not prove
the source or descriptor rules.

Failures include an invalid actual rebind/lookup, a changed result consumer,
loss of native return delimiters, use of pre-entry state after resumption,
repeated receipt, omission of the pending suffix or attribution of computed
callee requests to receiver invocation. An empty admitted domain makes the
pointwise target vacuous and proves no source-world inhabitance.

No second equivalent Call-coverage lift is attempted. Once the execution tree
reaches the independent carrier/return or pending predicate, construction
stops: source-image equations, a larger transition probe and an attachment
certificate would leave that same semantic implication untouched.

Recommended next action: provide the fixed `SEM_JOINT` carrier/provider-entry
and ordinary Return/Request clauses for this identity-entry instance, then
derive the terminal and pending consequences at their original incidences.
This is a request for the next proof input, not for a new language decision.

Unverified: `SEM_JOINT` construction, carrier/descriptor predicate clauses,
full local Call typing, body/consumer preservation, arbitrary finite prefixes,
recursive handles, world preservation, adapters, source-world inhabitance,
original association, whole-source coverage and production conformance.

## 7. Checks, resource usage and frozen dependencies

Checks: read-only `git rev-parse HEAD`; bounded section reads and `rg`
navigation; one Python process comparing eleven direct dependency byte strings
against `git show <baseline>:<path>` and computing SHA-256. All eleven matched
before writing; the leased output was absent. Initial aggregate captures
truncated; decisive assigned sections were reread narrowly. No absence claim
relies on an incomplete source search.

One leased Markdown note. No compiler/cfg(test), tests, builds, formatter,
manifest, lockfile, shared task/theory/index/authority or question edits.
No Git mutation, child process delegation or heavyweight calculation. At most
three independent lightweight read commands were submitted in one batch.
No numerical CPU/RAM/wall-time ceiling was supplied; usage was not instrumented.
Final dependency equality, path-local whitespace and freeze hash are reported
in the handoff. These are producer integrity checks, not independent review.

| Direct dependency | Baseline SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/theory/successor-proof-obligations.md` | `18bfa4e5bb461616ca17a0c9a1492f75ff7fca2f6231a13b3d68e0a3335136dc` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-07-original-association-conditional-call-lift.md` | `af3e95a760bee396a0f07d421d8fe2a8c775ab414b354abf15b103345d1cc46a` |
| `notes/progress/2026-10-07-successor-source-association-falsification.md` | `09a4aee423985c03f1365574e1d4572e67cc6b2f3f3c25fa747b711bbe304738` |
| `notes/progress/2026-10-07-original-association-constructor-derivation-attempt.md` | `bfd197a094a6fa3e813325a40c361687ed609ad45aa89af9908f58ce240b5435` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-07-call-type-local-law-constructive-attempt.md`.
- Baseline SHA: `035f7f8e97f5544ccd028bd1f167b83054134fdc`.
- Changed dependency hashes: none at pre-write verification; final equality
  recheck supplied in the frozen handoff.
- Review status: unreviewed producer attempt; conditional operational reduction
  and bounded premise localization only. No closed semantic gate.
- Checks already run: pinned authority/prior-attempt reads; eleven dependency
  byte/hash comparisons; leased-path absence. No executable semantic check.
- Proposed one-line research-checkpoint commit message:
  `research: isolate ordinary carrier elimination in Call typing attempt`.
- Shared-record deltas intentionally left for primary/curator: optionally cite
  the terminal/pending carrier-entry proof cut under `CALL_TYPE`; keep
  `SEM_JOINT`, `CALL_TYPE`, `ORIGINAL_ASSOC` and downstream gates open. No shared
  record changes are proposed as authoritative clauses.

Research writing stops before frozen review submission.
