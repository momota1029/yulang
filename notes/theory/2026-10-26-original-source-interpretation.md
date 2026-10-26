# Original source interpretation: selected joint operator and first source applications

## Status and exact result

This packet constructs the adopted positive immutable `V/W/T/Car` operator,
its greatest fixed point, its declared-value-hole relative construction, and
local applications of the already checked raw-source reconstruction theorem.
It does not instantiate the entire original seven-field source `Kernel`, prove
the original Rust generator satisfies that interpretation, or close original
Yulang inference soundness.

The code is
[`OriginalSourceInterpretation.lean`](lean/YulangClosure/OriginalSourceInterpretation.lean).
Its immutable input checkpoint is
`97788357754a57562607dd8ff41ac55ffcb3c9b8`. The accepted
`OriginalSourceSyntax` and `OriginalSourceGeneration` modules are unchanged.
The local source application is specifically an unannotated literal, or an
unannotated ordinary value-formal `Name`; it is not a replacement source
grammar or a declaration that other forms are unsupported.

The main new source supplier is `native_bind_supplies_name_constraints`.
The actual `SourceIdentityWorld.bindValue` constructor, its original lexical
read theorem, and explicit raw cell/result projections construct the generated
constraints of the ordinary value-formal `Name`. This supplier does not take
the desired generated constraints, source typing, or recursive membership as
a premise. `generated_name_membership` then uses the accepted source induction
and the independently obtained full current-world certificate to recover the
same installed value, descriptor, root, and current event.

## Governing selected definitions

The adopted authorities are
[`contextual-function-membership-definition`](../design/2026-10-08-contextual-function-membership-definition.md)
§§2–3, selecting
[`call-semantic-input-realization`](2026-10-08-call-semantic-input-realization.md)
§§2–4 and
[`simultaneous-immutable-root-introduction`](2026-10-08-simultaneous-immutable-root-introduction.md)
§§2–5. The source application uses L1–L5 and SRC in
[`source-generalize-definition-and-proof`](2026-10-08-source-generalize-definition-and-proof.md)
§§2, 6, together with the accepted raw-source construction in
[`original-source-generation-construction`](2026-10-26-original-source-generation-construction.md).

The selected membership definition explicitly says:

> The source context domain and complete descriptor admission/observation
> relations remain independent inputs. This selects their missing contextual
> introduction and callable-realization cases, not an exhaustive concrete
> definition of those entire relations.

Consequently, the input sorts and independent primitive relations remain
parameters here. This is not itself an obstruction to a parametric original
soundness theorem. It does mean that a caller cannot claim an authentic
original interpretation merely by filling arbitrary fields of `Inputs`.
Descriptor classification, original domains, registered field projections,
and source event correlation still need their actual identification.

## Decorated tuples and independent inputs

`Fiber` retains one original valuation `nu`, constructor graph `K`, dependency
assignment `D`, source graph, and binder tree. `Event` additionally retains
`eta0`, the actual `eta`, history, current configuration, current joint witness,
scope, authority, incidence, and dictionary. Current configuration and witness
are event fields; they are not frozen when a closure is created.

`ValueRow`, `CarrierRow`, and `TraceRow` retain their full descriptor/interface,
actual object or observation, original root where applicable, and event.
`Challenge` and `CallInput` retain the actual callable/root, complete carrier,
carrier root/view, context, continuation, receipt, typed path, consumer, and
incidences. `Challenge.retarget` changes only the checked Function descriptor;
`retarget_keeps_actual_input` proves its complete `CallInput` is unchanged.

The independent fields of `Inputs` have the following exact roles. None takes
the varying candidate `Family`, a source derivation, solver success, or final
query success.

| Input fields | Original responsibility and remaining identification |
| --- | --- |
| `compatible`, `eventCoherent` | Original admitted future/lifetime relation and exact joint event coherence. Their authentic source history and fixed-fiber correlation are not inferred from carrying an `Event` record. |
| `valueForm`, `ground`, `fixedExternal` | Authentic descriptor classification and independently fixed primitive/leaf relations. Ordinary Functions and carriers must receive their selected recursive cases; the API alone cannot certify an arbitrary classification. |
| `structuralGuard`, `structuralFields` | Independently registered other constructors, with every recursive field represented positively and at its original scope. |
| `actual`, `functionGuards`, `capturedFields` | Every genuine provider decomposition; full formation, role/entry, profile, scope and incidence guards; captured certificates at their actual roots/events. |
| `checkedInlet`, `actualInlet`, `carrierAccepted` | Independently fixed whole checked and actual inlet acceptance, before candidate membership. No successful body or eventual Return is part of inlet admission. |
| `puncturedContext`, `otherValues`, `registeredHoles`, `checkedIncidences` | Complete independently formed original `D_F` challenges. The actual argument carrier and its full incidence are retained. |
| `receiptPrecondition`, `actualTypedPath`, `actualContext` | Actual provider acceptance preconditions at that same complete input. They are not tested to shrink `D_F`. |
| `execute` | Every actual zero-step, administrative, pending, complete, and admitted-development observation of the fixed provider/input. Its output is a `RawObservation`, with no checked output interface. |
| `checkedObservation` | Complete original positive `P_F[Z]` readout indexed by the checked challenge and the same raw observation. It can require a different recursive result descriptor for a different checked Function. |
| `observationGuards`, `traceForm`, `observationFields` | All independent descriptor, guarantee, request/response, raw-handle, phase, scope, authority, incidence and joint-constraint guards; pure Return or unfinished shape; every remaining positive continuation/observation field. |
| `worldGuards`, `installed`, `installedCount` | The original registry/scope/current-authority/incidence guards and installed objects. `PhiW` quantifies every `Some` entry; count is allocation metadata, never a bound hiding certificates. |
| `alias`, `capture`, `captureValue` | Actual alias/capture object projections. Equal names or two absent cells do not establish agreement: equations require an actual `Some` installed value/carrier tuple including its descriptor/interface and root. |
| `sharedPosition`, `witnessAt` | Equality of original shared witness positions at the joint event. These still require the authentic source-position map. |
| `carrierGuards`, `carrierCaptures`, `demand`, `force`, `forceIncidence` | Original inert formation/license/view/scope/incidence, actual captures, all independent designated demands and all actual Force observations. Force uses an actual `CarrierInput`; the checked interface is attached only in the trace obligation. |

`Positive` explicitly represents fixed guards, recursive indexed fields,
conjunction, disjunction, universal domains, and original-scoped existential
evidence. `positive_mono` is an induction over those constructors. The caller
does not supply monotonicity. The census also checks a discriminator where
`forall challenge, exists evidence` succeeds, while swapping those binders
does not; no evidence is silently chosen before its dependencies.

## The actual four-component construction

`PhiW` includes event coherence, all four independent world guard groups,
alias/capture/shared-witness agreement, and every installed value/carrier
certificate. In particular, `world_installed` has no `i < installedCount`
premise. `nativeInstalled` separately gives the actual native allocated-cell
projection and proves that unallocated cells are absent.

`PhiT` checks the actual current world and all independent observation guards.
For pure Return it additionally checks the returned value at exactly that
event and original result descriptor/root. Unfinished observations have no
Return requirement. Both cases retain all additional positive observation
fields; this does not replace the full hard envelope by outward effect support.

`PhiV` checks the authentic selected descriptor case and hereditary restriction
at every independently compatible later event. Its Function case requires at
least one actual provider decomposition and checks every actual decomposition,
every original admitted challenge, actual inlet acceptance, and every raw
observation against the entire descriptor-indexed `P_F[Z]` clause.

`PhiCar` checks inert formation and all current captures/world fields, all
independent demands, all raw Force observations at the checked interface, and
hereditary restriction at the same object/root. It does not require that the
carrier eventually returns.

`phi_monotone` is proved from these definitions. `Greatest` is the union of all
postfixed families; `greatest_unfold`, `greatest_fold`, and `meaning_iff` prove
the actual fixed-point laws. `Meaning` is this constructed simultaneous fixed
point, not a field supplied by an original `Kernel` and not a definition of
source typing.

`ValueHoles` admits only exact value tuples. It has no world, trace, carrier,
authority, or arbitrary source-typing hole. `Background`, `background_lift`,
and `simultaneous_introduction` construct the adopted relative argument from
the actual operator. The last theorem still requires the actual added source
cases and exact replacement of the holes; this packet does not relabel that
premise as an implemented proof of the complete recursive pair or identity
Function. Those cases need the original complete guard/phase readout.

### Repair of checked-result indexing

The compiling check06 attempt was semantically deficient: its actual
`execute` relation returned a `TraceRow` that already contained an interface,
while a changed checked Function could affect only a candidate-independent
incidence predicate. This could not represent the original distinction between
the same raw `Return(unit,r,C,w)` checked at `PureReturn(Unit)` and at
`PureReturn(Bool)`.

The frozen code separates `RawObservation` from `TraceRow`. Actual execution
and event identity stay fixed. `checkedObservation` produces a positive clause
at the checked challenge, and `checkedTrace` can require that same raw
observation at its own recursive interface. `different_checked_trace_requirements`
proves that a candidate may validate the first interface and reject the second.
`checked_return_result` and `function_return_result` follow the actual checked
trace through `PhiT` to its own recursive returned-value certificate.

`same_provider_function_check` now requires transport of the whole
`ObservationMem inputs Z` clause from `P_A[Z]` to `P_F[Z]`, not merely metadata
inclusion or retargeting. This is the selected conditional Theorem F. It is
not installed as an opaque inclusion oracle in the source `Kernel`, and this
packet does not claim that the finite source checking rules already supply
that transport.

## Source and native applications, with their premise boundaries

| Declaration | Constructed conclusion | Genuine remaining inputs |
| --- | --- | --- |
| `immutable_rebind_world` | Full target world from actual immutable replacement/append data | Old full world, original compatible event, independent new-event guards/equalities, exact raw cell update and new binding certificate. A completed target world is not a premise. |
| `immutable_name_value` | Exact installed value/descriptor/root at the current event | Full current world and actual installed lookup. |
| `return_observation_iff`, `name_return_observation` | Complete selected Return clause | All original independent guards and additional positive observation fields. |
| `source_inlet_acceptance` | Actual provider inlet acceptance | Exact actual/checked inlet equality, independent checked admission, actual receipt/path/context facts. No body or output certificate. |
| `function_challenge`, `carrier_observations` | All original challenges/demands and observations | Existing same-operator membership. No narrower challenge domain or eventual-return assumption. |
| `ground_membership` | Ground value membership by an actual postfixed construction | Authentic ground classification, primitive relation, and its independent L1 hereditary law. |
| `generated_literal_membership` | Meaning of an unannotated literal through accepted source reconstruction | Its generated local clauses, authentic literal relation/classification, and the local ground law. |
| `name_constraints_from_binding` | Generated constraints of an ordinary value-formal Name | Actual name/address, allocated bound and exact raw installed tuple; no semantic membership premise. |
| `generated_name_membership`, `generated_name_return` | Meaning of that same Name and its selected Return observation | Generated clauses, full current world, and for Return its complete original guard/positive fields. |
| `native_bind_supplies_name_constraints` | Those generated Name constraints and actual native lexical read | Actual `bindValue` constructor plus explicit raw native/source name, count, cell and result maps. The maps do not assert typing. |
| `native_receipt_preserves_predicate` | Every predicate of the whole realized receiving record is unchanged by the accepted pending/executed materialization equation | Actual original receiving inputs. This is not yet an interpretation of all semantic receipt/path/world guards. |
| `native_dictionary_order` | Original ordered dictionary substitution action | The accepted dictionary word/action definition. No idempotence or type preservation is inferred. |

`SourceAssignment` keeps distinct `OriginalSource.Endpoint` ports. The local
applications read `.finalRoot` explicitly; they do not identify synthesis,
written targets, returned values, or other source-owned ports merely because
their solved scalar types coincide.

### Exact seven-field Kernel coverage

`literalKernel` and `nameKernel` are owner-specific local extensions of an
existing `Kernel`, not a claim to have constructed that full Kernel. Their
guards match the original source site and literal/name. Other atoms and all
other fields are retained from the supplied original Kernel.

| Kernel field | This packet |
| --- | --- |
| `atom` | Actual local `literalDeclaration` and ordinary value-formal `resolvedSameBinding`/`computedFetchOnce` cases. Their predicates contain raw declaration/lookup data, not `Meaning`, `Satisfies`, or the desired source derivation. |
| `admitted` | Not interpreted for the full generated binder telescope. The independent semantic `CheckedDomain` is constructed, but its exact heterogeneous source-payload correspondence remains. |
| `primitiveCheck` | Not interpreted. Authentic L1 declaration relations and finite L3 checking laws remain to be linked. |
| `structuralShape` | Not interpreted. Original child endpoint/constructor incidence, including optional records, remains required. |
| `functionShape` | Not interpreted. The complete same-provider theorem is available, but the finite domain/observation children and universal source binder must supply it through their actual interpretation. |
| `boundaryTag` | Not interpreted. Source-owned annotation/entry mode and distinct actual endpoint ports must be preserved. |
| `conversion` | Not interpreted. Each direct original registered conversion needs its actual law; optional-record boundaries cannot acquire transitivity. |

The accepted 13-expression/11-pattern/3-statement raw-source builder is
unchanged. Complete Call, effectful code, retained/published/imported Names,
recursive initialization, optional records/defaults, methods, rigid operations,
handler scopes, State, and native success-to-satisfaction remain in the original
parent goal. This packet does not remove or reject those forms.

## Next concrete supplier: scoped semantic payload and event decoding

The next gap is a finite source construction, not a need to redefine the
challenge domain. `SourceAssignment` currently interprets only the local root
in the two source cases above. Using a copy of that entire assignment as every
event's payload would be wrong if description evidence were allowed to vary:
`OriginalSource.EventStep.data` is part of actual event/anchor identity.

A separate packet should construct a heterogeneous payload and deterministic
environment interpretation using the existing unchanged `BinderKind`,
`ScopedValue`, `Environment`, `InitializerEntry`, and `PublicationRecord`.
The needed data maps are:

1. **One root assignment.** Fixed `Fiber`, `eta0`, source endpoint/declaration
   registry, original lexical/object projections, and initial actual event.
   Endpoint maps must preserve every `Port`; synthesis, final root, written
   target, callable image, returned value, formal carrier, body consumer and
   invocation-return ports remain distinct.
2. **Description payloads.** Data for `description`, `viewLogic`,
   `publishedInstance`, and `eventProof` frames, with original scope/dependency
   references. These are separate from actual runtime payloads. Extending one
   cannot change the actual event key or a captured initialization.
3. **Actual event payloads.** Complete invocation `CallInput`, receipt,
   Return/rebind or pending response, rigid operation instance, and one-shot
   data at their owning source site. Every original admitted payload must have
   an encoding/decoding equation. No stored anchor may normalize the arbitrary
   original challenge before admission or extension.
4. **Shared payloads.** Actual installed value/carrier tuples and original
   witness/dependency projections below the initializer's actual response
   telescope. Their common identity is fixed across descriptions, while a new
   actual invocation keeps its own source origin, parent path, occurrence and
   complete payload.
5. **Environment fold and publication maps.** Decode the actual ordered frames
   into the live semantic event and logical assignment. Replay starts from
   `entryPath`, `entryNames`, and `entryFrames`; `fixedFrames` remains separate
   lookup history. Actual completed captures remain distinct from the entry
   lexical environment. Alias uses the same publication identity and object.
6. **Exact admission correspondence.** Prove both directions between the
   original independent domain and the appropriate scoped payloads, then
   interpret `admitted`. Prove description extension and replay preserve raw
   input/observation identity and original correlation. The admitted domain
   must not be merely the events already present in the anchor map.

This enables a genuine interpretation of finite `Checking`: `functionShape`
can identify the actual same callable, domain child and descriptor-indexed
observation child, while recursive finite checking proofs supply the full
domain/observation transport. It must not assert those inclusions itself.
The returned Unit-versus-Bool discriminator above remains a required case.
Only after this map should the remaining original constructor atoms be
connected to their authentic L1–L5 local laws and native source owners.

## A genuine specification boundary, without declaring parametric closure impossible

The selected membership authority explicitly leaves concrete W/Z grammar and
unknown State laws independent. The governing
[`source-contracts-and-common-allowance`](../design/2026-10-05-source-contracts-and-common-allowance.md)
§3.7 says that the whole-tuple W/Z relations are not selected there and that
their validity/certification remains an explicit primitive-design obligation.

Its own finite illustration gives the precise distinction: with independently
admissible whole tuples `x,y`, `G={x,y}` and source base `R={x}`, the choices
`W=empty, Z=empty` and `W=empty, Z={y}` yield respectively `{x}` and `{x,y}`.
The second admits an independent non-source alternative under the same full
hard guard. This is an illustration of the unchosen grammar, not an actual
Yulang source counterexample or a license to add a convenient Bool return.

Both possibilities can remain parameters of a source theorem with the genuine
L1–L5 laws and exhaustive alternative accounting. The immediate next missing
payload/environment interpretation does not depend on choosing between them.
Likewise, a concrete mutable transition cannot be declared compatible merely
because the immutable world theorem applies to some other transition.

## Verification and frozen evidence

The checks used only the owned isolated cache/TMPDIR, the exact authorized
Lean 4.35.0 toolchain, one thread, `-j1 -M1024`, and a 120-second timeout per
focused invocation. No old module, project import, native implementation,
dependency, configuration, or expected output changed. There were no child
agents and no Git operations in this packet.

Nine focused Lean invocations were consumed from the cap of twenty. Checks
01–04 retain their actual syntax/elaboration failures. Check05 succeeded.
Check06 succeeded with four unused-simp warnings but its semantic
observation-indexing attempt was superseded after independent review. Its
source snapshot is retained with SHA-256
`a963d7f31ad1878c906578794481dd373f949268dc0fb797f9fe3b16ac47802b`.
Check07 compiled the semantic repair with those warnings. Check08 compiled the
frozen code with empty diagnostics. Check09 printed the complete originating
type and axiom census, including private/generated declarations.

The census contains **816 originating declarations**, **281 theorem
declarations**, and **48 required public theorem roots**. Every originating
declaration has a complete paired type/axiom entry. No project axiom, `sorryAx`,
or dependency outside `propext`, `Classical.choice`, and `Quot.sound` was
accepted. Check09 has no errors or warnings. A postprocessing-only attempt
initially rejected universe-decorated pretty-printed axiom names; its failure
is preserved, and the parser now normalizes only that printing suffix. The
Lean census itself checks actual axiom `Name` values and passed unchanged.

| Frozen evidence | SHA-256 |
| --- | --- |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| Checked `OriginalSourceInterpretation.olean` | `8e92d28b7b3743addbdc8877ca9ca33c6ac015d3ddfeac7092e6154448736cb0` |
| `OriginalSourceInterpretationAudit.lean` | `e3c0706506e49446a7e9964383bb217005a2a81e611cae6ed48f5a500a4b99c8` |
| `check09-originating-census.log` | `c24bead7be9b80174b0293771bb68843d45311d6c875f818237ccf903102961a` |

The exact input source/compiled hashes, audit summary, all diagnostic logs,
superseded bytes and complete census are under the owned
`/workspace/scratch/f98087c7ac1a/source-interpretation-r4/` directory. Independent
semantic review remains the acceptance gate; this author note is not its
receipt.
