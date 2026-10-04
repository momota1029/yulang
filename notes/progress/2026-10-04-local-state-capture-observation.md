# Bounded local-State capture observation

Date: 2026-10-04. Scope: one stable-core source fixture; no new general State
transition rule and no implementation authority.

## Direct fixture evidence

`tests/contracts/stable-core/v0/run/vm/pass/ref_update_local_buffer_public/main.yu`
creates a local `$buffer`, then creates both a `get` closure that reads
`$buffer` and an `update_effect` closure that writes `&buffer`. It invokes
`r.update` and only afterward calls `r.get()`. The fixture's expected
`stdout` is `run roots ["start!"]`.

Thus, for this concrete same-invocation source path, the callback captured
before the update cannot behave as a closure over the immutable initial value
`"start"`: the required later read returns the updated value. The observable
fact is established by the stable-core contract fixture; this record does not
claim a fresh test run.

The source architecture independently states that `StateSlotId` is a static
origin, not runtime activation/cell identity (§6.9), and that `&a = value`
uses pure continuation restart rather than primitive in-place mutation
(§8.3). Read together with the fixture, the narrow path requires the captured
read and update to meet the replacement data for that execution. This is
compatible with current data through a captured reference, but does not make
the static slot ID itself the dynamic state identity.

A second fixture, `tests/contracts/stable-core/v0/run/vm/pass/example_refs`,
updates two local declarations independently and expects `(11, 21)`. This
supports distinct updates for two visible slots in one lexical execution; it
does not identify runtime activations across calls or establish alias behavior
for escaped/multi-shot closures.

## Exact remaining boundary

The fixture does not define the general transition relation: how dynamic State
ownership is created and selected; what data an escaped closure reads after
the owning scope exits; how distinct activations of one static slot remain
separate; or how restart interacts with raw and repeated multi-shot
resumption. The frozen `RefSet` path is characterization only and does not
fill these successor source rules. Keep captured references, dynamic State
instances, and continuation branches distinct.

The next proof slice is to derive this one fixture path from the intended
State/update and callback invocation expansions, then retain its exact limits
when extending to activation and resumption closure. Do not reopen the
same-invocation old-value question for this fixture; ask for a new semantic
choice only if the source expansion leaves one of the remaining cases
undetermined.

## Frozen Oracle expansion characterization

Read-only inspection of frozen main at commit
a58eefc31e22141574b6f20c6a5748151c6d79f1 found the public implementation in
`lib/std/control/var.yu`. Its `ref.update` method repeatedly invokes
`r.update_effect()`; the `ref_update::update v,k` handler clause calls `f v`
and passes its result to the saved continuation before looping. The `var_ref`
constructor connects `get` and `set` to the State operations and builds
`update_effect` as `set:ref_update::update:get()`. The frozen runtime fixture
is a distinct custom `ref` record: its `get` closure reads `$buffer`, and its
`update_effect` closure evaluates `&buffer = ref_update::update $buffer`.
That fixture does **not** call `var_ref`; `var_ref` is a separate State-backed
implementation in the same library file.

This source adds the concrete library-control-flow shape behind that one
Oracle path. It is implementation characterization only: neither the
`loop:k:f v` structure nor the operation-handler decomposition is adopted as a
general successor rule. For the fixture, the callback result flows through
the saved continuation into the local `&buffer = ...` assignment; the
separate `var_ref` State `set` handler is not on this execution path. The
successor derivation must show how that assignment's pure continuation
restart composes with callback resumption and how the captured `get` later
reads the replacement. The stable-core expected output independently fixes
the final `start!` observation; this inspection did not run the fixture.

For the callback literal at `r.update (\old -> old + "!")`, the successor
contract remains the approved role-first rule: the known callback context
selects Handler before body constraints; parameter/body/result endpoints are
formed independently under normative B; the completed interface is checked
once by ordinary `F_lit <: F_cb`. This is a new literal-introduction path,
separate from adapting an already constructed Pure value. The Oracle body does
not prove that Pure-value inequality.

The inspected expansion still does not give successor equations for dynamic
local-slot ownership, distinct activations, escaped captures, or multi-shot
resumption. The separate `var_ref` body cannot fill that gap for the custom
record in the fixture. The expansion also does not construct whole-carrier
admission or prove either Function-domain inclusion. The next bounded proof
remains the same-invocation fixture derivation: connect callback resumption to
the local assignment's replacement and derive the later captured read from
the selected State source clauses. Keep raw callback resumption and State
restart as distinct transitions.

## Bounded successor derivation audit

A Sol architecture audit of the same-invocation path found the exact missing
bridge. Ordinary continuation composition can deliver the callback response
to the saved assignment suffix, but it does not perform State replacement;
the architecture's pure continuation restart does not yet specify how a later
read through the pre-existing capture observes that replacement. The
unproved obligation is therefore:

```text
WriteLocal(s, v, K, C) -> RestartLocal(s, v, K, C')
  implies that a later read through the existing capture of s,
  reached by K in this invocation, returns v.
```

This is an obligation schema, not an adopted transition rule. `s` denotes the
visible declaration origin and is not runtime activation identity. For the
fixture, the expected output fixes the instance `v = "start!"`; it does not
choose a general dynamic-State representation. The conditional trace still
requires a successor `ref.update` expansion premise, callback-response
delivery, ordinary raw resumption, the separate local-assignment restart, and
the captured `get` read. No `var_ref` equation belongs to this custom-ref
path.
