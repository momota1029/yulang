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
