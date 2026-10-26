# Retained Computation parameter: native bind, Shared and complete world clause

This checkpoint proves the **plain post-receipt Computation bind** for the
computed native interpretation. It stores the actual delayed carrier with
`interface = Computation`, the selected receipt view, and `dispatch = None`.
It preserves old cells, saved captures, aliases, the selected parent's dispatch,
receiving state, control and residual native data. The same registered carrier
Shared is consumed by the original decoder, and its whole installed map agrees
with the fixed native `Inputs` after that bind.

The complete `PhiW` proof is applied to both `Meaning` and `Background` (`B_H`).
Their final consumers derive the pre-bind world from the **same whole-carrier
certificate**; they do not require a separate old-world validity premise.
No Force, Return, eventual termination, pure-result equation, or completed
checking theorem is substituted for the retained carrier certificate.

The checked source is `lean/YulangClosure/OriginalRetainedParameter.lean`,
namespace `YulangClosure.OriginalRetainedParameter`, SHA-256
`ae8915cf002019541d0658895f0604e98700ac23f47aac479fc8382cf65ef799`,
55,668 bytes. Source writes stopped at
2026-10-26T17:07:07.192712+00:00 after clean check 11. This file adds the second
entry mode without changing the earlier Value bind or any existing source.

**Exact remaining boundary:** the Shared decoder updates `Decoded.installed`
and keeps its Event unchanged. The computed post-bind native Event has its new
snapshot and assignment. The theorem `retained_decoder_matches_native_inputs`
proves the full installed-map equation and explicitly proves that the delivered
decoder's Event is still the prior Event. It does not assert that this is already
an actual source/native transition or the full original inference theorem.

## 1. Original authority and actual machine projection

The source authority is SG §3.3 in
`2026-10-08-source-generalize-definition-and-proof.md`, together with the
Entry-Retained rule of `2026-10-07-call-input-construction-proof.md` §3.2.
The formal description is fixed before the invocation and receipt. Retained
carrier evidence belongs at the original retained Shared owner. EventFields
and description-owned EventProofs remain distinct. The call-input realization,
simultaneous immutable root §§2–5, and recursive-original-interface embedding
§§3–6.3 preserve the independent history domains and the fixed interpretation.
Embedding §6.2 allows defining a genuinely missing native presentation; it does
not permit replacing arbitrary already fixed original `Inputs`.

The exact Rust projection was read before constructing the new operation:

| Actual source | Represented action and limit |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs`, Computation branch around 1299–1333 | Optionally call `receiving.enter`, record its receipt, then bind `delay`, selected `view`, `ParameterRole::Computation`, `dispatch: None`; enter the body afterwards. This branch does not call `execute`. |
| `machine.rs`, `extend` and `bind` around 2626–2640 | Append one populated cell and one environment node, retaining the selected parent's dispatch. |
| `runtime/receiving.rs`, `enter` around 224–260 | Allocate RootComp boundary/image/view records. This allocation and its HIR/source correspondence are not implemented by the new module. |
| `runtime/receiving.rs`, `receipt` around 261–278 | Append the actual owner/view/slot/formal record and update its index. The accepted `Receiving.record` projection is applied directly. |

`packet` and `bindRetained` model the plain bind after preprocessing, using its
actual selected parent. They do not model environment substitution, construction
of the selected RootComp view, or body evaluation. The native receipt insertion
is optional in the Rust branch when a schema is absent; the generic bind does
not invent an extra receipt in that case. `actual_receipt_then_plain_bind`
models the branch with an actual receipt insertion, after any view construction.

The projection uses the supplied original `Parameter`'s resolved name as the
native binding key. Its native receipt uses the Lambda slot, while the original
source receipt binder uses the formal's site. Those are preserved as different
coordinates. No equality between an HIR identity, a source slot, a semantic
inlet and a formal descriptor endpoint is inferred merely from similar names.

## 2. Exact native storage and old readout preservation

`packet delay selectedView` is exactly
`⟨delay, computation, selectedView, none⟩`. `bindRetained` pushes that record,
without the `asValue` conversion in the accepted Value-entry constructor.
`stored_carrier_record`, `retained_native_vector`, and
`retained_preserves_native_fields` prove the stored record, actual vector
extension, selected-parent dispatch and untouched represented native fields.
`retained_formal_lookup` proves lookup/shadowing for the same actual formal key.

`installInterface` changes only the interface interpretation at the newly
allocated address. It leaves every descriptor interpretation and the native
value/carrier/root maps unchanged. A contract belongs to an address and view;
view equality alone is not a typing certificate and cannot identify different
cells' contracts.

`retained_bind_readout` proves the full function equation

```text
bindingReadout(postAssignment, postStore)
  = extendBindings(bindingReadout(preAssignment, preStore), freshAddress,
      carrier(preselectedInterface, actualCarrier(delay), actualRoot(delay))).
```

It is proved from `Store.push` and the actual vector representation. There is
no post-readout equation in the assumptions. Freshness is derived from that
vector representation, not assumed as a semantic domain restriction.
`fresh_interface_keeps_old_readout` and `retained_all_old_cells` preserve every
old populated cell. The semantic installed map still reads **every `Some`**;
it is not filtered by `installedCount`, successful lookup, reachability or
membership. The finite vector premise describes this actual native allocation
constructor, not every arbitrary original background world.

Captures use the closure's actual saved environment and the resolved body
reference. `retained_capture_address` preserves that address even for an older,
nonlatest environment shadowed by the new formal. `retained_capture_readout`
proves the **complete decorated value or carrier readout** under the changed
interface assignment, using the actual address invariant and old-cell support.
This is stronger than merely preserving an address or reusing a theorem with
an unchanged assignment. `retain_capture_value` applies it to every registered
provider lookup in the fixed native `Inputs`.

## 3. Formal Interface, original receipt and one retained Shared

`selectedInterface` reads the Computation branch of the original `Contract`
from `Selected`; the `FormalAssignment` takes only the original parameter,
source introduction route and complete supplied pre-invocation `ScopeValues`.
The actual carrier, receipt, fresh address and future behavior are not selection
arguments. `selected_interface_before_receipt` makes that independence explicit.

`declareInterface` replays the accepted complete `Telescope` and updates the
Interface namespace at the original `Parameter.coordinate.endpoint`.
`selected_at_original_interface` proves that local equation.
`interfaceDescriptionFrame` constructs the actual Description frame with its
complete supplied actual-event and entry-path metadata;
`decode_interface_description` proves that the original decoder consumes that
frame to produce this declaration.

This is a constructed local source-frame consumer. The accepted Telescope
checks binder/kind and retains all supplied Frames, but does not by itself
prove arbitrary enclosing source-occurrence or event-parent incidence. The
formal's source annotation is retained by `Parameter`; evaluating an arbitrary
annotation to this formal Interface remains an original registration obligation.
In particular, the formal endpoint in `Decoded.interfaces` is not silently
identified with `.formalCarrier` or `Inputs.actualInlet`.

`receipt_owner_is_source_generated` unfolds the actual root-Lambda source
owner traversal. It obtains its original receipt at local route
`[0,0,0,0]`, with all preceding Description, ViewLogic and Invocation entries.
The body and pattern are arbitrary original sources. No global Site freshness
or successful typing is used.

`NativeReceiptKey` retains the complete original `RawKey` as well as the actual
native delay, selected parent and selected view. The original key retains the
declaration, introduction route, every complete raw parent step, occurrence and
whole receipt record. The extra native delay prevents a noninjective semantic
carrier interpretation from collapsing distinct native inputs. Interfaces,
world validity and description proofs are not raw key fields.

`CarrierPosition` is a separate typed strategy argument. It retains the
Parameter and complete Selected prior tuple and contract, the source-owned
retained position and its full local Lambda prefix, and the lossless native
receipt key. `carrier_position_keeps_entire_formal_scope` proves that no supplied
outer formal values or preselected contract are dropped. This retention does
not authenticate those supplied outer scopes as arbitrary generated source
occurrences. The local prefix is built with the real Description, ViewLogic,
Invocation and Receipt payloads. Computation mode does not append a Return.

One `CarrierAssignment` application at that complete position computes the
Shared witness. `scopedCarrierEvidence` computes the actual fresh address and
retained carrier/root at the fixed formal Interface. `source_scoped_retained_delivery`
selects the formal contract before entry, computes one witness, and delivers
exactly that Shared through the original `decodeFrame` action. It proves the
whole installed-map equation, the source formal's binding and preservation of
the entire older fixed-frame prefix.

The accepted annotated generation surface produces exactly one delivery.
`retained_scope_has_no_return` preserves the source owner's virtual route
`entry.route ++ [2]` and the different physical insertion route
`entry.route ++ [0]`. They are not silently identified, and no second Shared
is cloned for another proof description. `two_proof_uses_same_retained` keeps
proof-use sidecars separate; preceding typed scope fields may genuinely affect
the supplied original strategy.

The actual invocation-to-native carrier/root relation is **not invented**.
`invocation_readback_retained_object` records the precise data equations under
which the computed retained object agrees with the actual invocation fields.
Those equations remain a real source/native supplier when an arbitrary original
invocation is presented. Neither an unexplained membership predicate nor desired
world validity is hidden in this data lemma.

## 4. One fixed native Inputs and the complete post-bind PhiW

The accepted `OriginalParameterSemantics.inputs base references` is reused
unchanged. It was defined on the missing-native presentation before invocation.
Its installed, capture and alias fields are computed from native cells and
saved references. Every nonworld input is inherited unchanged: checked domains,
raw Force relation, trace form, observation fields and all carrier behavior.
No new `Inputs` or arbitrary registry is selected for a returned address.

`retainEvent` computes the actual new native snapshot and fresh-address
interface interpretation. Its fiber and initial assignment remain the same;
current history, logical assignment, witness, scope, authority, incidence and
dictionary come from the independently supplied current `EventFields`. The
base scoped Shared strategy is retained at the same old positions. This does
not freeze the entire witness or require all current EventFields to remain equal.
Native receiving/control/rest and opaque residual configuration are preserved
by this plain bind projection.

`retain_installed` gives the computed total installed equation at that Event.
`retain_old_installed` transports every old `Some`. `retain_aliases` reads the
original saved alias environments; it does not infer aliasing from equal raw
values. `retain_capture_address` and `retain_capture_value` use the actual
provider closure table and same cell. Malformed records remain data in the
presentation; the constructor's valid saved-environment bounds are explicit.

`retain_phiW` proves **all** original `PhiW` conjuncts:

1. The independently supplied current event coherence and primitive world guards.
2. Old shared-reference aliases read the same actual installed object.
3. Every actual capture address is in the extended native store and its captured
   object equals the same installed readout.
4. Repeated base scoped Shared targets read one strategy value.
5. Every installed `Some` is valid in the candidate family at the common new Event.

For a general candidate, its recursive inputs are the prior `PhiW`, a genuine
restriction action on each actual old value/carrier, and the actual new carrier
field. These are clearly candidate-relative premises. It does not assume the
post-world clause, an arbitrary registry commutation, a blanket local safety
law or all-world validity.

## 5. Carrier-derived Meaning and Background applications

The stronger completed consumers discharge the generic world/restriction
inputs using the actual carrier certificate. For a carrier row `c` at `before`,
`PhiCar` contains `Z (.world before)` and hereditary carrier membership at every
compatible later Event. `carrier_meaning_current_world` unfolds the greatest
fixed point and extracts its actual current world. Its `Background` counterpart
unfolds `RelativePhi`; a Value-hole branch cannot prove a carrier row.

`retained_meaning_world` requires:

- the actual finite vector and valid saved provider/alias environments;
- the selected native parent, same delayed carrier, selected view and preselected
  formal Interface;
- the original compatible-event relation and primitive coherent/world guards for
  the computed post-bind Event;
- **one whole carrier certificate at that Interface and the prior Event**.

It derives the old world and uses the completed interpretation's own hereditary
action on all old installed objects and the new carrier, then folds the complete
computed post-bind `PhiW`. There is no separate old-world premise and no Force,
Return, eventual-return or `traceForm = pureReturn` premise.

`retained_background_world` does the same with `B_H` and its own hereditary
action, with the original hole-future closure condition. Carrier and world rows
cannot use a Value hole. Ordinary `Checking.sound` is not used as a hole-relative
inclusion. The same complete carrier certificate retains effects, pending
observations and all later demands through unchanged `PhiCar`.

`source_formal_retained_meaning` applies the consumer at the actual constructed
formal Description endpoint. Its carrier premise is read at that endpoint; the
proof rewrites with `selected_at_original_interface`, retains the whole supplied
prior binder list, and binds the source formal's exact name. It does not claim
that an arbitrary actual-call inlet already supplies that formal-interface
certificate. That is the precise next original entry readback obligation.

## 6. Decoder agreement and the remaining actual Event transition

`retained_decoder_matches_native_inputs` proves three facts together:

```text
delivered.installed = fixedInputs.installed(computed post-bind Event)
delivered.assignment.event = prior Event
delivered.assignment.binding(formal name) = fresh native address.
```

The prior installed equality is an explicit induction invariant. The accepted
native `initialRoot` constructs its initial case, but this module does not reset
an existing source Environment to manufacture that invariant.

The middle equation is intentional. An original Shared payload installs evidence
but does not run a Runtime frame or change the Event. Thus this checkpoint does
not claim `Meaning.world` at that decoded Event after a complete original entry.
It proves the computed native world and the exact same-cell decoder data link.

A next local constructor can compute a receipt Runtime whose `after` contains
the actual post-plain-bind native snapshot, compute fresh-interface logical
readout from the pre-bind Event, and then apply this same Shared. That can prove
the decoded Event equation by unfolding the actual constructors. The original
source/native incidence still matters: Rust records its receipt before the plain
bind. An accepted combined retained-entry receipt boundary must justify the
post-bind `after`, or an explicit source-owned suffix delivery is needed. An
already fixed receipt `after` cannot simply be overwritten. This is a concrete
correspondence obligation, not a proof of impossibility.

The legacy `sourceRules` and its successful Outcome/Environment semantics are
unchanged here. They are not claimed to emit the new annotated formal Shared
already. The primary's separate coordinated migration owns that connection.

## 7. Scoped-presentation and full-parent boundaries

The accepted native witness field still has domain
`SharedPosition b View`, while native `NS b ...` changes Configuration,
Assignment and JointWitness. Its strategy is not automatically a strategy over
all `ScopeValues (NS b ...)`. This packet retains all separately supplied typed
arguments in `CarrierPosition`; it does not construct the full dependent
base-sort/native-scope correspondence or identify those arbitrary positions with
every native `Inputs.witnessAt` target. Event record pack/unpack alone would not
prove that correspondence.

The native world clause therefore has its stated fixed base scoped strategy
interpretation. Complete original Shared ownership, all future EventField
suppliers and the source-wide transition induction remain separate. So do the
actual `receiving.enter` view construction, HIR/source projection, formal
annotation/inlet certificate and body execution. These boundaries are not
removed by the valid local receipt, bind, decoder or fixed-point proofs.

No source modes or arbitrary original history/provider domains were removed.
No alias/capture lookup or raw admission is filtered by typing or successful
execution. No opaque already fixed original interpretation is replaced. General
recursive L4, hereditary Function registration and complete inference soundness
are not conclusions of this checkpoint.

## 8. Discriminators and checked evidence

The source contains checked distinctions for nonlatest saved captures with
formal shadowing, selected-parent dispatch, exact Computation-versus-Value
storage, full captured contracts under the fresh interface update, identical
views at different cells with different carrier contracts, one native bind with
two distinct semantic Interfaces, changed current witness with older Shared
positions preserved, lossless native delays and complete raw parent histories,
and two proof-use descriptions of one retained position. No semantic validity
is inferred from these raw distinctions.

Author verification used the pinned native Lean 4.35.0/Lake5.0.0 toolchain, an
isolated copied cache and immutable input checks. It did not claim a fresh
empty-cache dependency review. Thirteen of the eighteen permitted bundles ran;
all source/config snapshots and failures were retained. Every bundle had a
120-second limit, one CPU/thread, `-j1 -M1024`, and a 1280 MiB group RSS cap.
Maximum elapsed time was 9.29 seconds and peak group RSS 1,168,199,680 bytes.

Check 11 built the frozen module. Check 12 enumerated every originating constant
by actual module index, including private/generated declarations, and all actual
current-audit declarations. It printed full explicit types and transitive axiom
dependencies. Check 13 imported the compiled audit and enumerated that module
and the new current audit:

| Inventory | Count |
| --- | ---: |
| Originating constants | 130 |
| Originating theorem constants, including generated | 68 |
| Authored theorem roots | 48 |
| Actual current declarations in the first audit | 0 |
| Compiled first-audit declarations | 0 |
| Actual current declarations in the closure audit | 0 |

Only standard axioms occur. Across the 130 constants, `propext` occurs in 40
closures, `Quot.sound` in 16 and `Classical.choice` in 3; among the 48 authored
roots the respective counts are 31, 16 and 3. There are no project or unapproved
axiom dependencies. This is not an axiom-free claim.

The producer receipt records every failed and successful run, source-to-theorem
mapping, immutable input manifest, complete census locations and exact residual
owners. Independent nonauthor review and primary integration are separate gates.
