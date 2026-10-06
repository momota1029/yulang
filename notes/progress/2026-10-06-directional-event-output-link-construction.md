# Directional event-to-output link: constructive inversion and source cut

Date: 2026-10-06
Baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`
Status: frozen bounded research result; compiler-referee reviewed with no findings
Method: constructive rule/schema inversion for one ordinary Apply
Claim class: bounded dependency characterization and conditional decorated derivation
Semantic/implementation authority: none
Exclusive lease: this note only

## 1. Objective and result

Conditional on the original seed and static `NewProtection` bridge, determine
whether a concrete request from the selected invocation can be source-linked
to that original upper-view output-effect occurrence. Keep the original
`beta`, scope `sigma` and whole `xi=(nu,K,D)` fixed.

The derivation reaches an execution contribution to the complete invocation,
but cannot construct its incidence at the original upper occurrence. The first
unproved source judgment is the **output-contribution specialization of P**:
realize the original directional introduction at `p_0` in the typed executing
view of this source Call. The remaining transport/observation theorem is
conditional on supplied profiles and typed correspondences. Per the assigned
stop condition, this note stops there; it introduces no source rule for P,
`Flow`, `Observe`, `Receive`, or receiver activation.

This is a precise derivation cut, not a source counterexample or proof that
no eventual source rule can close it. The selected directional meaning and
the static bridge are retained. No lower provider is newly protected by
backwards propagation.

## 2. Governing sections and explicit premises

Pinned governing reads:

- [Directional addendum](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
  §§1–6: original upper occurrence, no backflow, and separate event obligation.
- [Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
  §§1–5: source identity, shared assignment, provisional formal protection,
  Q independence, and open source-generation gates.
- [Callback delivery](../design/2026-10-03-callback-context-delivery.md)
  §§2–4: B, actual entry/role preservation, and invocation through a slot view.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§6,9: Name/Result/Apply skeleton, complete invocation, request suspension,
  and interaction directions.
- [Typed-boundary realization](../design/2026-10-02-typed-boundary-realization-draft.md)
  §6: supplied profiles/correspondences, typed transport, receipt, observation,
  `Path`, and exact current-configuration incidence.
- [Source-call construction](2026-10-06-source-call-generation-construction.md)
  §7 P; §§4–5 inspected only to fix the generated static constructor's scope
  and the explicitly supplied `TypedCallCert_Dec` premise.
- [Static Apply bridge](2026-10-06-directional-apply-output-bridge-attempt.md):
  the seed-conditional result and its explicit event/profile inversion stop.

Premises, with their claim boundaries:

**H0 — assigned static premise.** Use the same resolved component
`my apply f = { my step x = f x; step }`, with its only selected Apply
`c=Apply(u_f,u_x)`, original formal `d_f`, `v=A_f`, root `R_f`,
`beta=(d_f,R_f)` and `p_0=(beta,call.effect)`. The seed at this exposure and
the original `SourceUpperUse` yield
`NewProtection(k,beta,u_c,sigma,p_0)`. This premise supplies a static
introduction, not a completed original profile or event packet.

**H1 — conditional execution premise.** Consider a finite, independently
admitted execution prefix of this Call under the same whole `xi`, in which
the actual provider's complete execution reaches a concrete request `q`.
Existence, independent admission and source acceptance of that execution
are not proved here. Q success is not an admission constructor.

**H2 — retained ordinary core premises.** The actual provider keeps its own
role and entry; lexical resolution and Value bindings are the ones in H0.
Its complete execution includes its actual entry, reached body and designated
result consumer. Preserve event identity, origin, response endpoint, current
state and all dependent `K,D` through suspension/resumption. The reviewed
ordinary skeleton is used in its stated representation-preserving envelope;
an executable conversion requires its separate source judgment.

There is no candidate language assumption. The missing source judgment below
is an obligation description, not an accepted hypothesis or new carrier.

## 3. Proof tree and first unproved source judgment

The static branch is already conditional on H0:

```text
ProtectedVarAt(k,v,sigma,u_c)   SourceUpperUse(u_c,v,F_c,sigma)
Gen-Call-0(c): p_0 <-> p_out(c), with original beta and F_c
----------------------------------------------------------------
NewProtection(k,beta,u_c,sigma,p_0)                 [static only]
```

The execution branch follows the ordinary primitive equations under H1–H2:

```text
Name(x): Value(A_x)       Result(Value(A_x)) = Comp(empty,A_x)
----------------------------------------------------------------
Delay(J_x) is inert; actual entry owns its consumption

q is reached during the actual complete invocation
Request(q,C,k_q) >>= pending_suffix
  = Request(q,C, response => k_q(response) >>= pending_suffix)
----------------------------------------------------------------
the same q contributes to this reached complete execution prefix
```

For this exact `f x`, entry consumption of the rebound ordinary Name does
not recursively execute a latent `A_x`. No effectful-argument witness is
silently substituted for this source argument. The conditional request can
arise in the reached provider body or its designated result consumer.
Complete invocation includes these stages; it is not merely the closure's
body row. The equation does not require q to survive handler selection into
outward support. It preserves a reached request and its pending suffix;
it does not assign the request a target boundary profile.

The branches do not yet join. Their first missing join is:

```text
original c,beta,p_0,sigma,xi; NewProtection(...,p_0)
actual complete execution of c, including reached event q
--------------------------------------------------------------- ? P_output
the original p_0 introduction has its source-justified typed
incidence in the current complete executing view exposing q
```

`P_output` is a name for the needed specialization of source-call §7 P's
original contribution/path interpretation and same-root seed-to-refined
receiving-view normalization. It is not a proposed production predicate or
an additional axiom. In particular, `ElimOrigin` identifies a static
elimination address; source-call §4 explicitly denies that it is a runtime
`Flow`/`Observe` edge or packet. A decorated solution's
`TypedCallCert_Dec` explicitly *takes* profiles, receipt, observation and
correspondence premises; inverting it cannot generate them from this source.

Typed-boundary §6 then gives this **conditional**, later subtree:

```text
original realized profile chi_b(p_0,b)
matching source-derived Flow*(p_0,p_exec)
source-derived Observe(q,V_exec,p_exec)
matching Receive(u,slot,V_exec,corresponding-path)
--------------------------------------------------------------- Path definition
Path(q,u,b,p_0)

Path(q,owner(h),b,p_0)
Active(h,C) & Active(owner(h),C) & Active(b.receiver,C)
--------------------------------------------------------------- Inc_C definition
Inc_C(q,h,b,p_0)  =>  Protected(q,h,C)
```

Here `b` must be the actual boundary realization of the original profile,
not a boundary allocated by the static introduction. All middle ports,
source tags, view identity and receipt must match. Conditional `Observe`
must be pre-dispatch at the current complete view, rather than inferred from
the outward row. None of the four first-line premises is derived by this
note. Receipt/liveness are later cuts even after `P_output` is supplied.
The original receiver may have ended before a returned `step` is invoked;
H0 alone does not establish its activity. No dynamic protection conclusion
is asserted for that situation.

## 4. Discrimination, omissions and failure conditions

Solving an equal row at a provider lower occurrence and upper `p_0` cannot
join the two branches: equality records no upper source introduction, event
view, observation or ownership. Family equality and callable-pointer equality
also supply no matching typed path. Conversely, disappearance of q from
outward support cannot disprove its pre-dispatch observation. These are
logical omissions in such proposed shortcuts, not newly constructed
source-valid semantic counterexamples.

The conditional later subtree fails if the original occurrence is absent
from the realized profile, its map has no route to the executing port, q is
exposed outside that view, the candidate owner has no matching receipt, or
any exact handler/owner/original receiver is inactive. A latent later event
needs a separate result-view observation and matching signature path;
`call.effect` cannot be copied to `result.latent.effect`. A known external
Name supplies no unannotated-formal seed. Independently inherited provider
evidence survives; the proposed join cannot create reverse protection on it.

Coverage is one ordinary Apply and a conditional finite request prefix.
No source-wide P, full original slot inventory, arbitrary captured packet
attachment, annotated contribution permission, SCC seed timing,
generalization/instantiation theorem, arbitrary conversion, unknown/open
client domain, repeated-resumption owner mapping, complete admission A,
principality, production containment or implementation conformance is proved.
This method does not establish a runtime event exists or that a raw program
is accepted. It reduces the next required premise to the original occurrence's
typed executing-view realization.

## 5. Checks and frozen handoff

Reads used the assigned commit through `git show`; exact sections were
reinspected after an initial combined capture was truncated. Policy reads
covered `rules/research-lab.md`, `rules/design-authority.md` and
`rules/git-concurrency.md`. The dependency recheck used `git diff` against
the assigned baseline on the seven listed source paths; only the live
static-bridge review metadata and next-action wording changed, with no
rule-content change. This
derivation uses the pinned pre-review text and claims no independent review.

Baseline SHA-256 dependency hashes:

| Dependency | SHA-256 |
| --- | --- |
| directional addendum | `6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7` |
| inferred call views | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| callback delivery | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| typed-boundary realization | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| source-call construction | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| static Apply bridge | `eb769fc97930d6da23785c7c01102bc83a29daeb26186aae1c5374ca1da410ea` |

At the dependency recheck, the static Apply bridge's live hash was
`89f8b4c5522d799be0ef7e0dc7723549b91b232c6092bbc300133a2bf0077708`;
the delta changed its review status, added an independent-review record and
removed the completed review from its next action.
Primary integration must recheck that metadata delta and any subsequent
dependency changes. All other listed live hashes matched the baseline.

Note-only relative-link existence and trailing-whitespace checks were run.
No builds/tests, Oracle, solver, checker, mutation experiment, random seed,
range enumeration or measurement ran. Thus there is no executable oracle
independence claim: the derivation shares the governing source equations and
the static bridge's stated hypotheses. CPU, peak memory and total wall time
were not measured. Only lightweight reads/checks and this note write ran;
initial independent reads overlapped, with no heavyweight process or generated
build output. No other path was written. The artifact is frozen at handoff.

Recommended next action: assign a source-constructor method for `P_output`
on this exact generated root, requiring a derivation of the executing-view
incidence from original source evidence. Reapplying transport to a supplied
map would leave the same premise untouched.

## Independent review

A compiler referee reviewed this note against the selected directional rule,
typed-core execution equations, typed-boundary realization and source-call
§7 P. No blocking, major or minor findings were reported. The review confirms
that the execution derivation preserves a reached request but does not produce
its incidence at original `p_0`, `Observe`, a matching `Receive`, or `Path`.
Source construction of that incidence, source admission, receiver activity,
and the production path remain outside the reviewed result.

Commit packet: exact lease
`notes/progress/2026-10-06-directional-event-output-link-construction.md`;
baseline `e12738d4f1452d87883516dfa5b709a4a5c38230`; changed dependency hash:
static Apply bridge `eb769fc97930d6da23785c7c01102bc83a29daeb26186aae1c5374ca1da410ea`
to live `89f8b4c5522d799be0ef7e0dc7723549b91b232c6092bbc300133a2bf0077708`
(review/next-action metadata only); review status: frozen, unreviewed research submission;
checks: pinned exact-section inspection, scoped dependency diff/hashes,
note-only link/whitespace checks; proposed one-line message:
`research: isolate the directional event output incidence source cut`.
Shared-record deltas intentionally left for the primary/curator: record the
reduced `P_output` obligation and retained receipt/observation/liveness and
admission gates; no task, index, theory, authority or question-board edit.
