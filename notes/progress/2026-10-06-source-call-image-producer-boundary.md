# Conditional source call image and the unresolved producer boundary

Date: 2026-10-06
Baseline: `8e11d3fdd743983f4cc052eabf40a2f901a8dc2f`
Status: research-only conditional factoring; architecture audit found no scope issue; semantic proof not independently reviewed
Scope: exact `apply/step` candidate's call constructor and Q-independent source generation
Implementation/semantic authority: none

## Finding

The open `T_c` leaf in the exact-candidate relational construction needs a
scope distinction. The *operational call image*, once an elaborated callable,
argument, complete invocation view, and typed incidences are supplied, already
has a conditional constructor in the reviewed typed-core package. The missing
part is the producer that maps the resolved source call and shared formal/use
component into those decorated inputs and the original admissible joint-fiber
envelope `Omega_S`. Treating `T_c` as one indivisible unknown obscures this
boundary; treating the existing constructor as a completed source rule would
overstate it.

## Conditional constructor derivation

For a supplied derivation of callee and argument and one fixed whole
`xi=(nu,K,D)`, typed-core §3 gives the source-call translation

```text
X[call(c_f,c_a)] = X[c_f] >>= (f =>
  let t = Delay(X[c_a], lexical references) in
  ExecuteCallable(f,t))
```

`ExecuteCallable` is the complete invocation image: it uses the callable's
actual entry and receiver, its receipt/rebind, body, and designated declared
result consumer inside the retained `CallView`. Typed-core §9 names this
complete `J_call` and explicitly distinguishes it from a closure's `J_body`.
Source-contracts §3.2 supplies the corresponding Call inventory row: callee,
inert whole argument, actual receiver/receipt, actual entry, body, designated
consumer, and invocation return.

Thus, **conditional on those typed inputs**, the whole-call image can be
interpreted compositionally without inspecting the result of the pending
comparison `Q`, choosing a witness from each port independently, or replacing
the actual callable's role/entry. Every relation row retains the same `xi`;
the bind and call constructors compose rows rather than projecting and
recombining their coordinates. This is a direct constructor composition, not
a proof that the source occurrence supplies its premises.

The typed-core package still leaves a separate gate after this conditional
constructor: a finite symbolic presentation of the complete `ExecuteCallable`
image and higher-order/store challenge relations (§9, final paragraph). The
constructor equation is therefore not a complete finite source-call relation,
an effective subtype algorithm, or evidence that arbitrary admitted source
histories have been covered. Source generation must provide the needed finite
presentation and its coverage/typing certificates.

An independent architect audit found no scope overclaim in this factoring and
confirmed this separate finite-presentation gate remains open. It did not
certify a source-generation rule, admission theorem, or production behavior.

## Exact missing source bridge

For the approved source candidate, resolved structure provides the outer
formal `d_f`, inner formal `d_x`, use `u_f -> d_f`, use `u_x -> d_x`, call
occurrence `c=Apply(u_f,u_x)`, and the returned closure's lexical capture.
The ordinary core skeleton can place symbolic endpoints at those positions
and emit a whole-argument call obligation. It does not currently construct
the following mapping:

```text
(resolved component, c, shared formal endpoint, original source scope)
  -> (formal's role-indexed F_cb, static beta/Slots(beta), typed call incidences,
      original joint relation Phi_C, admissible fibers Omega_S,
      Q-independent admission)
  -> typed inputs for the conditional J_call constructor
```

The first arrow is the still-missing source-generation judgment. The second
arrow must preserve source/slot identity and provide the typed paths, owners,
receivers, and receipt schema that `J_call` consumes. The source occurrence
itself supplies none of those typed decorations. In particular, the
provisional Handler seed and ordinary-value evidence at `u_x` do not yet have
a specified operator connecting them on this shared relation. `Omega_S`
also cannot be defined by saying “all satisfying assignments of the
generated constraints” until the source producer and its joint constraints
have been constructed; that would be circular.

Method/role resolution can remain a later explicit premise: the conditional
constructor is parameterized by the supplied actual role, entry, complete
view, and typed links, and does not select them. This does not remove the
earlier obligation to construct the *inferred formal/use contract* and prove
its admission independently of `Q`.

## Claim limits and next proof obligation

This factoring does not close `T_c` for the source candidate or derive
`Omega_S`; it isolates the unproved source-to-decoration map. It does not
establish soundness, principality, source adequacy, complete admission, mixed
use aggregation, or production conformance. The typed-core document is a
conditional Draft for raw-source elaboration, and source-contracts is a
reviewed conditional package; neither supplies this constructor's missing
source premises. Frozen Oracle evidence is not used.

The next constructive attempt should derive the first arrow for the smallest
approved call component while keeping the role/entry and typed correspondence
as explicit unresolved coordinates. A result that can only proceed by
postulating the completed `F_cb`, `beta`/profile, receipt, or `Phi_C` has not
advanced the producer.

Method budget: one bounded authority/code-record crosswalk; no code changes,
builds, tests, runtime probes, randomized search, or performance measurements.
