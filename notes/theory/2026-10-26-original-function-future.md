# Actual future-invocation observation transport

Status: constructed and checked with a complete originating declaration audit.
Fresh independent review and repository integration are owned by the primary.
The result supplies the observation action at an actual admitted invocation,
including a later invocation. It does not establish hereditary Function
membership or complete original inference soundness.

Implementation: `YulangClosure.OriginalFunctionFuture`. Its sole direct import
is the accepted `OriginalCheckingAdmission` checkpoint. Existing source,
semantics, admission, and checking modules are unchanged in this packet.

## 1. Original obligation and scope

[SG §3.2(4)](2026-10-08-source-generalize-definition-and-proof.md#32-checking-and-actual-elaboration-rules)
requires a finite Function comparison to retain the actual callable and prove
both the complete checked-domain inclusion and observation inclusion at each
checked challenge. The displayed inclusions are conclusions of finite proof
constructors. They are not assumptions identifying successful resolver queries
with semantic membership.

The selected [call-input realization §2 and Theorem F](2026-10-08-call-semantic-input-realization.md#2-original-objects-and-the-noncircularity-boundary)
fixes the original static fiber and assignment eta0 while each independent
Initial, Response, raw Resume, or FutureUse history has its actual current
configuration and joint witness. Theorem F uses the same comparison at the
later complete challenge. Its §4.1 expressly prevents deriving an unrestricted
future certificate from a current-only assertion. The selected
[contextual membership definition](../design/2026-10-08-contextual-function-membership-definition.md)
retains all these original observations, providers, scopes, and future
restrictions.

The predecessor admission packet repaired the descriptor mismatch between
source binders and intermediate checking goals. Its GoalAdmitted predicate
already decodes the current configuration carried by a raw invocation. That
configuration can differ from the environment's earlier event. The predecessor
current Function theorem needed a view-token presentation and an event-readback
law for arbitrary semantic challenges. Neither law is needed when starting
from an actual admitted raw candidate, because the candidate already carries
the real token and its event is computed by the original decoder.

## 2. Constructed actual-event suppliers

`invocationEvent` uses the existing RuntimeReadout.event with exactly the
original decoded fixedFrames prefix, the before-event, the actual binder, and
the raw invocation. It does not re-root the environment.

`invocation_event_fields` proves all ten Event coordinates:

| Coordinate | Constructed value |
| --- | --- |
| fiber, eta0 | Original before-event coordinates |
| history, current configuration | Actual incoming raw invocation |
| eta, joint witness | Their readouts at the full original prefix and incoming invocation |
| scope, authority, incidence, dictionary | Their corresponding readouts at that same prefix and invocation |

The theorem identifies the actual data maps; it does not claim those maps have
already been constructed from every original source event declaration.
`invocation_event_redecoration` shows that Invocation.decorate preserves this
computed event. In particular it does not freeze the before-event witness.

`invocationChild` is the ordinary Runtime frame step followed by retain.
`invocation_child_preserves_prefix` proves that its fixedFrames are precisely
all previous fixed frames followed by the new original frame, including its
binder, complete ScopedValue, and entry event path. The existing Shared witness
frames are retained. CallOwner registration and descriptors are unchanged.
`decode_actual_invocation` identifies this child with the existing decoder's
actual Environment.extend operation.

`invocation_child_active` proves that the child's active CallInput is the raw
challenge's complete input at the computed event. Its descriptor parameter is
arbitrary because descriptor retargeting does not alter a CallInput. It does
not assume that checkedIncidences is invariant under retargeting.

## 3. Finite Checking supplies the actual later observation action

`admitted_checked_observation` quantifies over the actual Inputs, guard registry
and declaration interpretation, RuntimeReadout, LocalAdmissions, PortReadout,
original kernel, environment, enclosing goal, observation goal, and invocation
binder. Its substantive premises are:

- The original environment decodes to the supplied state.
- The binder is an invocation and the child goal is an observation goal.
- The actual candidate is GoalAdmitted at the enclosing goal.
- The extended environment has an actual finite Checking proof of the
  observation goal in the accepted registered proof kernel.

The theorem recovers a raw invocation and proves its complete payload identity,
the same original CallOwner callable value/root, its own checked target domain,
and the action

```text
P_observation.lower(raw challenge at its actual decoded event, output)
  -> P_observation.upper(the same raw challenge/event/output).
```

The action uses the completed Meaning family. The child semantic induction
hypothesis is obtained by the existing full finite Checking recursion, then
applied to the active actual input. The intermediate
`raw_observation_action` is merely the definitional active-input readout;
it is immediately applied to the checked child in the public result.

`function_observation_child_at_actual_event` directly consumes the observation
premise of Checking.function: for every candidate admitted at the enclosing
goal, there is a finite child derivation in its extended environment. It
produces the actual-event action for any such admitted candidate.

There is no token-choice premise, eventReadback equation, desired future
GoalMeaning, full FunctionShape premise, phase equality, or target-domain
invariance. The original target's complete CheckedDomain is retained. No source
syntax, provider alternative, guard, observation, or pending behavior is
excluded. This theorem is an application of the accepted registered proof
kernel; it is not a new construction of all original raw structural or Function
registrations.

## 4. Exact remaining domain-reading obstruction

The existing OriginalSourceChecking.stateClause at a domain probe is

```text
input.event = state.assignment.event
  AND CheckedDomain(input, endpoint descriptor).
```

Consequently its extracted DomainMeaning and its full domain GoalMeaning are
current-event assertions. A raw invocation's GoalAdmitted predicate can instead
use a later event computed from its incoming current data. The observation
supplier above handles that later event, but the current-only domain induction
hypothesis does not establish the required domain inclusion there.

EventDiscriminator is a finite model of the present formal interfaces. It is
not a source program and does not refute original Yulang soundness. Descriptors
and carriers are Bool. Its independent carrier admission is

```text
interface = false OR event.current = false OR carrier = false.
```

At the earlier event both descriptor domains admit both carriers. At the later
event the false descriptor still admits both, while the true descriptor admits
only false. Both domains stay nonempty at both events. The same callable value
and root are used throughout.

`current_domain_meaning` proves the earlier domain inclusion.
`current_goal_meaning` proves the entire decoded domain GoalMeaning for every
PortReadout, not only the extracted DomainMeaning.
`later_raw_is_goal_admitted` proves that the later carrier=true invocation is
actually admitted at the checked false descriptor.
`later_domain_inclusion_fails` proves that this same challenge is absent from
the source true-descriptor domain at the later event.
`future_input_excluded_by_current_guard` identifies the precise current-event
guard that discards it from the earlier domain reading.

The raw later invocation's decoder changes history, current configuration,
eta, and joint witness; `actual_later_readout` proves its full event and
`static_scope_same_current_fields_change` proves that fiber and eta0 remain
fixed while these four current coordinates change. Thus the example does not
rely on an unrelated static fiber or a frozen witness.

## 5. Static scope is necessary but does not supply event registration

The existing value reading accepts every Event probe, without a static-scope
or original event-registration guard. RuntimeReadout.event always preserves
the before-event fiber and eta0. The general
`event_readback_requires_original_static_scope` proves this necessary condition.
An arbitrary Event with another fiber or eta0 therefore cannot be represented
by the current immutable-root decoder.

Even equal fiber and eta0 do not imply event readback. The model's
`same_static_scope_does_not_force_event_readback` keeps both coordinates and
all raw current data but assigns the wrong joint witness. The actual decoder's
witness is true at the later event; the unrelated proposed event's witness is
false. The two events cannot be equated. The same issue applies to the other
actual source-owned dynamic fields.

Existing CallOwner registration records the source occurrence, context, and
callee/closure endpoints. It does not provide equations for eta, witness,
scope, authority, incidence, or dictionary at every independent future history.
Opaque semantic sorts are not an impossibility argument: independent original
declaration laws may supply these fields. Those laws still need their actual
source owner and dependent telescope.

## 6. First constructive owner and proposed coordinated repair

The earliest owner is the original Event/EventField introduction in
[SG §3.3](2026-10-08-source-generalize-definition-and-proof.md#33-owning-rules-declarations-and-event-telescopes):
Lambda, Delay, and handler later-event binders own the actual event fields;
body/checking certificates introduce their separate EventProof witnesses.
The dynamic history constructors are the independent Initial, Response, raw
Resume, and FutureUse constructors of call-input realization §2. Their full
field and dependency rules must supply the following construction:

1. From the original scoped event/history introduction, construct its actual
   current event and every EventField projection, retaining the original
   fixed prefix, Shared witnesses, actual event path, and each declared
   dependency. EventProof witnesses remain at their permitted description
   and event scope.
2. Prove the coordinate equations for the existing RuntimeReadout at that
   original introduction. The equations identify eta, current witness, scope,
   authority, incidence, and dictionary with their actual source-owned fields.
   The raw current history/configuration supply their two coordinates.
3. At an independently admitted target challenge, construct its original view
   presentation and raw invocation from those fields and the target's own
   checkedIncidences. Derive event readback from the field equations. Do not
   assume a generic readback predicate in place of this construction.
4. Establish coverage of every original independently admitted future history
   at that telescope. Using only the image of an arbitrary decoder would
   silently restrict the original quantifier. Immutable identities or static
   fiber equality alone do not prove coverage or current authority validity.

After that source-owned registration exists, the domain and value readings
need a coordinated event-scope repair: the domain action should apply at every
original lawful checked event, while value probes should range over the same
original fixed-fiber/eta0 telescope. Simply removing the domain equality leaves
the arbitrary unrelated Event problem. Simply adding a same-fiber test leaves
the dynamic field-owner problem. A lawful-event interpretation must be
constructed independently of desired value membership, provider acceptance,
or observation safety. It must preserve every original future alternative.

The current DomainMeaning and current Function results can then be recovered
by specializing the lawful-event action to the current registered event. This
is a proposal, not an implementation in this packet: all existing core bytes
remain frozen. Future target guards/captures and complete original Function
registration still require their own declaration-specific finite suppliers.
The general recursive L4 obligation remains separate and open; neither of the
previously rejected generic checking-closure laws is invoked.

## 7. Verification and exact boundary

The code was frozen after check 5 at SHA-256
`e90f98aa00597cf46089f2152b492ab98b21b0ab5350276410b622931439c99f`.
Native Lean 4.35.0 / Lake 5.0.0-src+eb6cafb checked the isolated imported cone.
Check 6 printed the full type and axiom dependencies of every originating
constant, including generated constants: 39 declarations, 24 theorem constants,
and all 20 authored theorem roots. Actual axiom union is propext and Quot.sound;
Classical.choice does not occur in this module's audited dependencies.

All six invocation snapshots and logs are retained. Check 1 was a native Lake
installation-resolution failure inside the restricted execution environment.
Checks 2 and 3 were finite-model elaboration failures: explicit History numeral
types, an id reduction, and the distinction between reflexive binder equality
and True. Checks 4 and 5 compiled cleanly; check 6 completed the full audit.
There is no project axiom, sorry, admit, unchecked native evaluation, or kernel
bypass in the delivered file. The paired handoff records exact commands,
resource bounds, file manifests, and the independent-review boundary.
