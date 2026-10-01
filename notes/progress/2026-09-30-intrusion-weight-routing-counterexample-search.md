# Effect routing counterexample search: helper boundary

Date: 2026-09-30
Status: source-level soundness conflict and compatibility delta established for
the repeated shallow-callback slice; not a complete effect proof or
implementation authority
Frozen Oracle: Yulang2 `main` at `a58eefc31e22141574b6f20c6a5748151c6d79f1`

## Purpose

The current gate treats Oracle weight routing and runtime guard routing as
evidence. This note records a targeted search for a mismatch where an explicit
callback effect contract crosses an ordinary helper boundary. It does not
derive the successor's effect semantics from Oracle's `StackWeight`,
`SubtractId`, or marker plan.

## Candidate: callback effect hidden by a helper adapter

The frozen Oracle accepted this source with an explicit pure result contract:

```yu
act choose:
  our reject: () -> int

my rejecter() = choose::reject()
my invoke(f: () -> [choose] int) = f ()
my via_helper(f: () -> [choose] int): [] int = catch invoke(f):
  choose::reject(), k -> k 3
  v -> v
via_helper(rejecter)
```

`check` succeeds, but both interpreter and evidence VM report an unhandled
`choose::reject`. `dump --poly-raw` gives `via_helper` a pure return-effect
endpoint (`Bot`); it preserves `[choose]` on the callback argument. The
monomorphized body wraps `invoke` in a `FunctionAdapter` with
`hygiene[body[add_id[0, choose, own]], arg[add_id[1, choose, own, resume-own]]]`.
The surrounding catch has no `marker[choose]` in this body. The same callback
handled directly by `catch f ()` returns `2` in both VMs.

Two boundary controls narrow the discrepancy:

- Changing only `invoke`'s callback row from concrete `[choose]` to wildcard
  `[_]` makes the caller's pure result annotation fail with
  `effect filter mismatch: choose is not allowed by []`.
- Putting `catch f()` inside `invoke` with the concrete contract and resuming
  `k` also makes a pure result annotation fail. The callback is abstract and
  its continuation may perform another `choose` request, so this rejection is
  consistent with the shallow trace reference.

Thus the surprising case is specifically a concrete capture budget crossing a
helper call and being subtracted by a caller catch: that program passes the
pure filter, but the runtime adapter's guard prevents either the caller catch
or an outer catch from handling the request. These controls narrow the routing
path but still do not identify whether constraint weighting or runtime guard
transport is causal.

### Source-pipeline localization

A read-only source trace narrows the candidate further:

- In `--poly-raw`, the finalized `invoke` scheme already has a pure return
  effect even though its body directly calls the annotated `f()`. The caller's
  `via_helper` scheme inherits that pure effect. The direct-handler control
  has the same callback contract, but its catch scrutinee remains a direct
  `f()` call.
- The monomorphic helper call is adapted from a callback returning a
  `[choose]` thunk to a callback returning a plain `int`. Its adapter carries
  `body[add_id[0, choose, own]]` and an argument resume marker. The helper
  catch body is an `App`, so `specialize2/marker.rs` does not add a direct
  `marker[choose]`; the direct control has a forced thunk and does get that
  marker. This explains the emitted shape but is separate from solver weight
  semantics.
- Concrete and wildcard callback annotations lower differently in
  `annotation/constraints.rs::lower_arg_effect_bounds`: the concrete row
  creates a positive `push(choose)` and a negative filter, while wildcard
  `[_]` keeps an unstacked effect variable at that callback boundary.
- `YULANG_TRACE_SUBTRACT_ALL=1` reports seven subtract IDs for the helper
  fixture and three for the direct fixture; all originate at concrete or
  empty callback-row annotation lowering (`annotation/constraints.rs:676,
  :685`). Neither fixture allocates an ID in the unannotated-local-callee
  return-effect path. These counts locate annotation-generated stacks but do
  not establish how a particular weight reaches the application result.

The effect is absent from `invoke`'s finalized scheme before the caller's
catch is specialized. At this point the CLI evidence alone did not expose the
constraint chain; the disposable bound-record trace below narrows it further.

An environment-gated bounds trace is a first partial view of that chain. On
the combined direct/helper fixture, `YULANG_TRACE_VAR_BOUNDS=0,...,120` with a
bound limit of 20 emitted 2,078 lines. Across those snapshots, the only
nonempty directed weights observed were left-side entries for `SubtractId(0)`
and `SubtractId(3)`, each a single `push(choose)`; no right-side entry was
observed. The snapshots include variable endpoints and current bound weights,
but omit bound-record IDs, structural parents, and origins, and they do not
name which source slot an internal variable represents. This is frozen
Oracle characterization of propagation, not evidence that left-only routing
is semantically correct or the cause of the finalized pure effect.

A disposable `infer` test then mapped the `invoke` body call to its typed
callback parameter and queried bound explanations. For
`my invoke(f: () -> [choose] int) = f ()`:

- the call to `f` is the `f ()` source application and its declared callback
  result effect is the concrete `[choose]` row;
- the `invoke` function body's return-effect node is
  `NonSubtract(Var(TypeVar(29)), StackWeight { filter: Set(choose),
  id: SubtractId(0), pops: 1 })` before scheme serialization;
- `TypeVar(29)` has four lowers and one upper. One lower is `Var(TypeVar(23))`
  with left weight `push(choose)` for the same `SubtractId(0)`;
- the explanation for that lower reaches both an `Annotation` origin and the
  `ApplicationArgument` origin whose source span is `f ()`. Its structural
  path includes `LowerStackNormalization` and `FunctionReturnEffect`, plus
  binary-bound replay. No `RowDerivation` edge appears on this explanation
  path.

The finalized `invoke` scheme still serializes its return effect as `Bot`.
This identifies the observed inference erasure more narrowly: a positively
weighted callback effect reaches the body return-effect graph, then the
matching non-subtract pop/filter remains on the function return endpoint and
the closed scheme is pure. This is a concrete Oracle cancellation path, not a
semantic justification for `push` followed by `pop`. The path does not use
row-residual splitting, so a proof of that row rule alone would not certify
this case. The runtime adapter separately carries an own-path body marker and
an argument resume marker; the candidate runtime escape is therefore still a
cross-phase inconsistency, not proof that this exact cancellation rule is the
sole defect.

The same disposable test mapped the call to `invoke` and its caller effect
slots. The call's pure instantiated return-effect variable enters the
application result-effect variable unweighted, with a
`FunctionArgumentEffect { pure_passthrough: true }` structural derivation and
an `ApplicationArgument` source at `invoke(f)`. That result-effect variable
flows unweighted into the `via_helper` body effect; no `choose` family or
`RowDerivation` edge appears on this path. Therefore the caller catch does not
subtract this `choose`: it is already absent from the helper's use-site
effect. A separate temporary runtime trace below maps the first catch skip.
This is a precise frozen-Oracle mechanism trace, not a proof that its weight
transformations are sound.

### Repeated-operation callback witness

The generic-callback soundness risk is now concrete. This source type-checks in
the frozen Oracle:

```yu
my two_requests() =
  my first = choose::reject()
  choose::reject()

my invoke(f: () -> [choose] int) = f ()
my via_helper(f: () -> [choose] int): [] int = catch invoke(f):
  choose::reject(), k -> k 3
  v -> v

via_helper(two_requests)
```

The checked `two_requests` scheme has `ret_eff = [choose]`; both `invoke` and
`via_helper` still have pure (`Bot`) return effects. In the declarative shallow
trace semantics above, the caller catch receives the first request and its
arm resumes the raw callback continuation. That continuation reaches the
second `choose`, outside the shallow catch. The exact outward support therefore
contains `choose`, so `via_helper` cannot soundly promise `[]` for every
callback satisfying its annotation. This does not require exact inference of
request counts: a conservative finite-family abstraction retains `choose`.

Both Oracle execution backends currently report an unhandled `choose::reject`
at the first request, before the intended catch can resume it. That runtime
result is consistent with the emitted adapter guard blocking the caller
handler, but differs from the source-level eligibility rule: the explicit
callback capture contract exposes `choose` to this handler. Thus two issues
must stay distinct: inference erases the callback's effect at the `invoke`
scheme boundary, and the current adapter guard also prevents the caller from
handling the first request.

This is now a concrete Oracle compatibility conflict with soundness. The
successor rule for this source envelope is to propagate `choose` out of
`invoke` because its body calls an effectful callback without a handler, then
retain `choose` from `via_helper` because resuming a shallow handler may reach
another request in the raw continuation. Consequently the explicit `[]`
annotation on this generic `via_helper` must be rejected. This records a loss
of frozen-Oracle acceptance for a source it accepts today; the source is not
well-typed under the successor's sound finite-family effect abstraction.
The contract/weight cancellation path and adapter-marker issue remain
characterization findings only: neither `push/pop` nor the runtime guard is
accepted as a semantic rule on Oracle authority alone.

Focused commands on the frozen checkout were:

```text
target/debug/yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-repeated-callback-body.yu
target/debug/yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-repeated-callback-body.yu --poly-raw
target/debug/yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-repeated-callback-body.yu
target/debug/yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-repeated-callback-body.yu
```

The check and dump exit successfully; both runs exit with
`yulang.unhandled-effect` at the first `two_requests` operation.

A temporary runtime trace confirms why the current operational path skips the
caller catch on that first request. The request reaches `eval_catch` with
`handler_boundary = None`, guard IDs `[3, 0, 1, 2, 4]`, and carried guards in
that order. The first carried guard (ID 3) has `entry_frame_len = 0` and no
exposed IDs; later preserve-enabled guards expose prior marker IDs, but none
introduces the catch activation. `request_guard_for_path` therefore returns
`Preserve(GuardId(3))`, and the matching `choose::reject` arm is skipped.
This matches the earlier source flow: function-adapter argument markers are
combined with body markers, while ordinary `eval_catch` has no registered
handler activation for `push_contract_matching_handler_ids_at_marker_entry`
to expose. The trace is direct runtime characterization; the Yulang3
successor should define handler eligibility from the declarative semantics
and must not copy this routing behavior by default.

With the declarative callback contract honored, the first request is eligible
for the visible caller catch. Resuming its raw shallow continuation reaches
the second operation outside that catch. The sound finite-family effect
approximation still includes `choose`; the pure annotation is rejected. The
runtime's current first-request escape is a separate guard bug and does not
make the pure type sound.

The source-contract basis is stronger than runtime behavior alone:

- frozen `spec/2026-05-31-effect-variable-subtractable.md` describes a concrete
  contravariant callback row as a `take` budget that permits a matching
  `catch f()`;
- frozen `web/docs/reference/effects.md` says a function acquires effects it
  calls unless a visible handler consumes them, and explicit callback
  annotations govern which effects may flow across higher-order calls;
- frozen `spec/2026-06-13-runtime-guard-markers.md` requires a guard frame to
  unwind when effect search exits it, allowing an outer handler to receive the
  request.

### Provider/capture contrast

The simple nested-provider pair changes whether the inner function's callback
parameter has an explicit capture contract:

- Without a concrete callback capture budget, `outer(rejecter)` passes through
  an inner same-family catch and returns `[1]`; the outer arm handles the
  request.
- With `inner(f: () -> [choose] int) = catch f(): ...` and an outer same-family
  catch around `inner(rejecter)`, both VMs return `[2]`; the inner arm handles
  the request.

This confirms that operation-family equality and nearest dynamic activation do
not determine eligibility by themselves. The annotation changes the visible
capture budget. The original no-budget probe and its trace are recorded in
`notes/progress/2026-09-30-intrusion-oracle-latent-effects.md`.

An independent `spec_auditor` found that these rules strongly support
compositional capture across the helper, but found no exact two-annotation
example. An independent `compiler_referee` confirmed the accepted pure scheme,
unhandled runtime request, and direct-handler control. Both cautioned that the
precise source of the mismatch is not yet localized to weight routing alone.

The repeated-operation witness establishes the compatibility conflict for
this callback slice: the frozen checker accepts a pure scheme while a
well-typed callback can leave a request outside the shallow handler. The
successor should honor the explicit capture contract for handler eligibility,
handle the first request, and retain `choose` in the outward approximation
because resumption may reach another request. The frozen runtime's first
request escape remains a separate handler-guard defect; neither runtime
behavior nor the current weight cancellation defines the successor rule.

Relevant source ownership candidates are frozen
`crates/infer/src/lowering/expr/tail.rs` application-effect construction,
`crates/infer/src/lowering/control.rs` catch subtraction, and
`crates/specialize/src/hygiene.rs` FunctionAdapter guard planning. Runtime guard
unwind is in `crates/mono-runtime/src/runtime/flow.rs`. Current evidence does
not establish which phase is causal.

## Controls: repeated calls, one shared frame pop, shallow resumption

The paired source calls one local callback twice through the ordinary helper:

```yu
my twice(x, y, f) = (f x, f y)
my effectful(x) = choose::reject()
my through_handler(f: int -> [choose] int) = catch twice(1, 2, f):
  choose::reject(), k -> k 3
  v -> v
through_handler(effectful)
```

The finalized `through_handler` scheme retains a stack-weighted `choose`
residual (stack quantifier `#1`, stack entry containing `Set(choose, [])`).
The interpreter and evidence VM report an unhandled request after resumption,
consistent with shallow semantics: a matched request's raw continuation can
reach the second call without reinstalling the catch. A control whose operation
arm ignores `k` returns `(3, 3)` in both VMs, showing that this source shape can
match and abort a request. The resuming run alone does not expose which dynamic
occurrence escaped. Separate source instrumentation already established
that `twice` produces two pushes of the same local-frame `SubtractId` with one
frame pop; that identity observation does not prove cancellation. Here the
scheme's residual and runtime trace agree, so this case is not a counterexample
to Oracle routing.

## Independent rule candidate and next proof

The declarative semantic reference is occurrence- and suffix-sensitive:

1. An explicit callback capture row is part of the callable boundary contract.
2. Ordinary helper application transports that contract compositionally; it
   must not silently turn a visible effect into an unhandled request while
   retaining a pure result effect.
3. A shallow handler handles one matching request. It evaluates the operation
   arm with the raw continuation; later requests in that continuation remain
   in the outward effect support unless an outer eligible handler consumes
   them.

This semantic reference predicts whether the one-request helper can be caught
and requires the repeated-call continuation to retain its later request. It is
not a requirement that inference compute exact suffix support. A conservative
sound inference abstraction may retain `choose` and reject the pure annotation
if the capture path is not proved. Principality is relative to the bounds that
abstraction can express; linear/affine continuation tracking is out of scope
unless separately justified by language design. The reference still needs a
source typing judgment, provider/handler ownership relation, and a soundness
proof for its abstraction. The first fixture's `FunctionAdapter` and effect
annotation must be traced to the exact left/right weighted constraints before
saying the candidate is specifically caused by `StackWeight` routing.

### Conditional finite-family transfer lemma for shallow handlers

This subsection makes one part of that reference precise without using Oracle
weights. It is a conditional candidate lemma, not the full source semantics:
the exact set of families a handler is authorized to consume at a call
boundary is an input `C` and remains a separate open obligation. Here `C` is
not merely the set named by an annotation: it contains only families both
authorized and completely covered by matching operation clauses. A partial
handler cannot drop a whole family in this abstraction.

Let `Fam` be the set of effect-family identities and let rows in this small
abstraction be finite subsets of `Fam`. `E` is an upper bound on all families
that may be requested while evaluating computation `e`. For a handler arm,
`A(E)` is the ordinary inferred effect support of its body in an environment
where the raw continuation `k` has latent row bounded by `E`. `C ⊆ Fam` is the
set of families this handler may soundly drop, after combining complete
operation coverage with the still-unproved source-level boundary-eligibility
rule.

The candidate transfer is:

```text
Eff(catch_C e with arms) = (E minus C) ∪ A(E)
```

The continuation is shallow: `k` denotes the raw suffix of `e`, outside this
handler. Typing `k` with latent support `E` is conservative because every
suffix trace is a suffix of a trace of `e`, hence its family support is a
subset of `E`. Ordinary application typing adds that latent support to `A(E)`
whenever an arm resumes `k`; no linearity, exact request count, or special
continuation-use analysis is required. If the arm does not resume `k`, `E` is
not added by this mechanism. Families in `E minus C` can escape without being
consumed, and arm-generated effects are included by `A(E)`.

For a fixed solution of the continuation/arm constraints, soundness follows by
case analysis on a finite execution prefix. An unhandled family from `e` is
in `E minus C`. The first eligible request in `C` is handled and is not itself an
outward request. Its clause's requests are in `A(E)`. If the clause resumes,
every request in the resumed raw suffix is bounded by `E`, and ordinary typing
of the continuation call includes `E` in `A(E)`. Repeating this argument
covers any finite number of shallow re-entries. The proof is only about
family support; operation payload/result types and handler eligibility require
their own preservation lemmas.

For principality relative to this abstraction, rows range over the finite
powerset lattice `P(Fam)` ordered by inclusion. Given exact abstract inputs
`E`, `C`, and the least arm result `A(E)`, the formula is the least sound
family-set output for the concretization that admits every computation whose
support is bounded by `E`: each family in `E minus C` can escape, and each family
in `A(E)` can be generated by the handler arm. This is a local best-correct
transfer claim, conditional on `A(E)` itself being principal and `C` being
correct. Recursive effect constraints would still require their own monotone
least-solution argument. This is not a claim of a principal source type until
the typing rules and eligibility relation are fixed. It also does not assert
exact trace support: an opaque callback with row `E` may receive the entire
`E` as its raw continuation bound even when some concrete callback suffixes
are smaller.

The repeated-callback fixture supplies the critical witness. Its `E` contains
`choose`; the operation clause resumes `k`; therefore `choose` occurs in
`A(E)` and remains in the outward row even though `choose ∈ C`. A pure result
annotation is rejected. This matches the sound source-level conclusion
recorded above and conflicts with the frozen Oracle's accepted pure scheme.
For the one-request/non-resuming case, if the arm returns without calling `k`,
emits no `choose`, and the handler completely covers and is authorized for
`choose`, then `A(E)` has no `choose` and the handler may remove it. An
incomplete handler keeps `choose` in `E minus C`, even if the particular observed
request matches one of its clauses. Thus the rule does not indiscriminately
retain every completely handled effect, and does not erase a partial family.

No left/right weight rewrite follows merely from this set equation. Any future
weighted encoding must prove that projection of every source constraint into
and out of `C` implements this transfer. In particular, Oracle's observed
`push(choose)` plus matching pop cannot be treated as its proof. Remaining
proof obligations before this becomes a usable source component are: define
`C` from callback annotations and nested provider boundaries; include unknown
rows and family payload constraints; prove monotonicity of the whole arm
constraint operator; and compose this transfer with the graph/type SCC
semantics. The construction is a candidate semantic component, not
implementation authority.

## Focused probes

All commands used `/tmp/yulang-intrusion-oracle/target/debug/yulang`; sources
were temporary files under `/tmp` and no frozen checkout files changed.

```text
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-via-helper-pure-annotation.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-via-helper-pure-annotation.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-via-helper-pure-annotation.yu --mono
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-via-helper-pure-annotation.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-via-helper-pure-annotation.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-capture-direct.yu
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-capture-direct.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-capture-direct.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-nested-inner-capture-direct.yu
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-nested-inner-capture-direct.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-nested-inner-capture-direct.yu
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu --mono
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-repeated-callback-abort.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-repeated-callback-abort.yu
```
