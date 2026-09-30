# Effect routing counterexample search: helper boundary

Date: 2026-09-30
Status: source characterization plus candidate semantic contradiction; not an
accepted soundness proof or implementation authority
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

An independent `spec_auditor` found that these rules strongly support
compositional capture across the helper, but found no exact two-annotation
example. An independent `compiler_referee` confirmed the accepted pure scheme,
unhandled runtime request, and direct-handler control. Both cautioned that the
precise source of the mismatch is not yet localized to weight routing alone.

This is a **candidate soundness/handler-visibility counterexample**, not yet a
proved violation of the complete frozen contract. If the intended declarative
rule permits the explicit `[choose]` budget to cross `invoke`, the successor
should route this one request to the catch and return `3`. If the helper
boundary instead prevents this catch from consuming the callback effect, then
`choose` must remain in the outward effect bound and the `[]` annotation must
be rejected. The frozen checker currently accepts the pure annotation while
runtime leaks the request. This precise accepted-source/runtime difference is
the compatibility behavior that must be resolved before choosing either
successor rule; no behavior was changed here.

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
yulang --no-prelude --no-cache check /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu --poly-raw
yulang --no-prelude --no-cache dump /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu --mono
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-repeated-push-shared-pop.yu
yulang --no-prelude --no-cache run --interpreter --print-roots /tmp/yulang-intrusion-weight-repeated-callback-abort.yu
yulang --no-prelude --no-cache run --evidence-vm --print-roots /tmp/yulang-intrusion-weight-repeated-callback-abort.yu
```
