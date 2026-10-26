# Original Value entry: actual Force supplies the native world premises

Date: 2026-10-27. Baseline: `6148fc868565617d7db6ef193a6ff164700d88f7`.
Branch: `yulang3`. Status: independently reviewed local Lean construction.
Original whole soundness, Effect hygiene, principality and inference termination
remain open.

`lean/YulangClosure/OriginalForcedParameter.lean` preserves the previously
constructed, unintegrated source exactly (SHA-256
`d16a45c459ea78b0f583ebd34d7a442d7247b55358ff6d990e3416c3d841aedf`).
Its original producer worked in the isolated `forced-parameter-r4` project.
The present integration rebuilt the module and rechecked all its theorem
types and transitive axioms; it does not rely on the old build receipt.

## Original claim and construction

Source Generalize §3.3 and the original Call input realization distinguish a
Value formal's real Force/Return from retained Computation entry. The
existing native bind theorem needed both the world before binding and the
actual returned value's semantic membership. These two inputs now follow
from the same independent whole-carrier certificate and its genuine force
observation.

`meaning_force_return_fields` unfolds the original simultaneous `Meaning`
at the carrier and its actual trace. It derives force incidence, membership
of that observation's world, equality of the returned row's event with the
observation, and membership of the actual returned value.

`background_force_return_fields` constructs the corresponding result in
the original hole-relative `Background`. It unfolds that operator directly;
only value queries can be holes. No completed finite-checking theorem is
reinterpreted as a theorem about arbitrary holes.

`bind_after_force_return_meaning` and
`bind_after_force_return_background` feed those derived facts to the actual
native `bindValue`/`bindEvent` world construction. They remove the separate
old-world and returned-value-membership premises from that application.
The original carrier may still have pending or diverging observations:
the theorems apply to a supplied actual Return, and do not assume that
every Force eventually returns.

## Boundary

The independent demand, force, and `traceForm = pureReturn` equations remain
original semantic inputs. The native cell-vector representation, saved
provider/alias bounds, selected lexical-parent lookup, compatibility,
event coherence, and world guards remain explicit. The descriptor argument
must still be linked to the source-selected formal contract. Global
source/native correspondence and recursive introduction are not supplied
by these four theorems.

## Fresh verification and review

Pinned Lean 4.35.0 accepted the module. The reusable
`lean/AuditOriginalFormalEntry.lean` audits this module together with the
formal-admission supplier: **65 originating theorem constants**, including
private/generated declarations, all required roots present, all complete
types and transitive axiom sets printed. The audit exited 0.

The force/Return field theorem uses no axioms; the Background field theorem
uses `propext`; both native bind applications use `propext` and `Quot.sound`.
There is no `sorryAx`, project axiom, unchecked native evaluation or kernel
bypass. New modules have no warnings.

The fresh nonauthor review is
[`2026-10-27-formal-entry-review.md`](../progress/2026-10-27-formal-entry-review.md).
It accepts these local statements and records every remaining source and
semantic owner. The combined audit log is retained at
`/tmp/yulang-formal-entry-audit.log`; the committed audit program reproduces it.
