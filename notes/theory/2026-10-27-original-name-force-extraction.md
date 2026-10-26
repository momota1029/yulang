# Original Name Delay: operational Force and observation extraction

Status: constructed and kernel checked for the explicitly selected Name-owned
interpretation below. Independent review remains with the parent. This packet
does not close original whole-language soundness, Effect hygiene, principality,
inference termination, or the complete runtime-to-source interpretation.

Proof module: `YulangClosure.OriginalNameForceExtraction`.
Frozen proof SHA-256:
`10ff6a2d4ac8a4a2c386396c495e0edfecc9bd4bb3ae40c8e0ab07e4cb0c7531`.
The leaf received baseline `e7551b9`; the input pins below, not an inferred
current Git status, identify the checked dependencies. No Git action occurred.

## 1. Result and the owner that changes

The prior `OriginalIdentityCarrier.NativeExtraction` required an execution
record, an `ObservationAt` record for every raw Force observation, and the
same raw observation's Force incidence. This module constructs those fields
for the actual registered lexical Name/Observe Delay constructor.

The operational part computes lexical lookup, initialized-cell read, raw
Name dispatch, view matching, receipt insertion, finite prefixes and the
Return descriptor at the computed cell address. `Independent.observationAt`
derives its `fuel`, `result`, `complete`, `event` and `form` fields; it does
not receive these conclusions. `force_incidence` derives incidence from the
same raw graph. `nativeExtraction` supplies the frozen Carrier interface, and
`name_delay_from_native_prefixes` applies `name_delay_whole` directly.

An opaque arbitrary `Inputs.force` and `Inputs.traceForm` cannot be inverted
from the available definitions. The chosen construction therefore instantiates
these owners at the existing `OriginalSourceInterpretation.Inputs` interface.
It is not a theorem identifying an arbitrary pre-existing opaque Force
relation with this concrete one. No old definition, Rust implementation,
original `Meaning`, `PhiCar`, `PhiT`, admission rule or source grammar changes.

The concrete observation sort is

```lean
Base b = { b with Observation := Sum b.Observation (Observation b) }
S b D ViewData Rest Body View =
  OriginalReturnWorld.S (Base b) D ViewData Rest Body View
```

The left tag retains every prior raw observation. The new right tag contains
only raw carrier/root identity, the captured `NameDelay`, an observation
budget, and the computed phase/address/received data. It contains no semantic
certificate, native-prefix equation or encoded `Meaning` proof. No encoder,
decoder inverse axiom or surjectivity premise manufactures the observations.
The prior base `Inputs` is selected on these concrete sorts; no isomorphism
with an arbitrary original opaque observation sort is asserted.

The four overwritten owners are precise:

| Field | Concrete definition |
| --- | --- |
| `force` | For a decoded lexical Name/Observe Delay, the graph of `observe ... n` for every natural observation budget. For every other owner, the old `base.force` relation. |
| `forceIncidence` | For that same owner, decode the right tag and compare its carrier, root, saved Delay and recomputed observation/event. Otherwise retain `base.forceIncidence`. |
| `traceForm` | Retain the left-tag readout. A right-tag computed Return reads its descriptor from the actual cell address and view; all other phases use the original `unfinished` constructor. |
| `observationGuards` | Retain all base guards; for the right tag conjoin the base phase guard with the concrete nonfailure phase test. Left-tag guards are unchanged. |

`other_force_unchanged`, `other_incidence_unchanged`,
`prior_observation_unchanged` and `other_owners_unchanged` establish the
literal preservation equalities. In particular `execute`, `demand`,
`compatible`, `carrierAccepted`, `checkedObservation` and
`observationFields` are unchanged. `checked_domain_unchanged` and
`actual_admission_unchanged` prove both directions for every original
challenge on the selected sorts. There is no admission-by-membership test
and no change of the original independent challenge domain.

These field equalities do not assert equality of whole `Meaning` for arbitrary
operators. Nor do they provide a transport theorem for an unrelated base
operation that already emits the newly reserved right tags. The authentic
runtime observation decoder must reserve those tags for this constructor;
all previous observation data remain available in the left tag. Other Force
and Execute relations are delegated as given, not filtered to obtain this
reservation property.

## 2. Exact source correspondence

The original obligation is the Name Delay case in
`2026-10-08-call-semantic-input-realization.md`, §4.3 Lemma D, with the
independent immutable-world and Return cases of §§4.1–4.2. Its carrier is
`Carrier-Delay(Code-NameValue(...), o_arg)`. The complete original carrier
and trace clauses remain those of
`2026-10-08-simultaneous-immutable-root-introduction.md`, §3, as represented
in `OriginalSourceInterpretation`. The admission/membership distinction of
`2026-10-08-outer-domain-carrier-provenance.md`, §3, remains unchanged.

| Native owner | Lean computation or explicit boundary |
| --- | --- |
| `machine.rs:1180`, `Frame::Callee` | The existing `OriginalIdentityCarrier.Allocation` retains the freshly allocated computation handle, exact Name code and saved lexical environment. `owner_from_allocation` reads that code back. Allocation does not execute an argument prefix. |
| `machine.rs:1224`, closure Value selection | The receiver enters its invocation, pushes `ValueEntry`, and calls `execute(delay, site)`. This packet starts at that designated Force cut; it does not simulate the receiver-selection prefix. |
| `machine.rs:2548`, `execute`; `:2551`, `execute_with_substitution`; `:2607`, `substitute_environment` | `execute` passes substitution `None`. The known Delay branch opens its saved code, and this particular substitution branch returns the same saved environment even when dictionaries exist. The model's Force-to-Name transition represents this owner. |
| `machine.rs:781`, `Instruction::Name` | `evaluate` performs resolved lexical lookup, distinguishes missing versus uninitialized cells, and retains the actual address/raw record. The selected resolutions are Parameter, Local, CatchBinder and CaseBinder with Observe consumption. |
| `machine.rs:2617`, `dispatch_name` | The selected dispatch result/error is `Native.dispatch`. `noDictionaries` computes the native early return that retains the raw record's existing dispatch. Dictionary-present mutation is an external boundary described below. |
| `machine.rs:2469`, `consume` | Match the view/value before appending the Name receipt; Observe returns the raw received record. Execute consumption remains with the original base owner. |
| `receiving.rs:261`, `receipt`; `:293`, `matches_value` | `finish` uses the existing `Receiving.record`: one append at the old receipt length, actual current owner/view/site, formal `none`, and index update. View bounds and mismatch are separated. |
| `machine.rs:2635`, `bind` | `capturedByBind` and `captured_by_bind_bound` derive the actual new cell address, initialized record, nearest lexical binding and Value mode. |
| `machine.rs:1438`, `Frame::ValueEntry` | Callback-entry view construction, unit/record pattern handling, post-Force parameter bind and body selection remain outside this local Force interpreter. |

`owner` checks the raw carrier handle, the actual optional executable entry,
its exact Name source body, and the native resolution/consumption readout.
Module-definition lazy initialization, Execute consumption, imported,
unresolved and ambiguous resolution, non-Name code and differently annotated
source bodies all delegate to the base. The original constructors remain in
the language and retain their existing owners. This is the scoped Name case,
not a claim that all accepted carriers are Name delays.

The raw handle/executable/name-mode readers must still be extracted coherently
from the actual native state and source resolver. Merely assigning them
matching values in an arbitrary model would not establish source
correspondence. `owner_from_allocation` discharges executable readback for
its explicit allocated constructor, not every raw decoder's correctness.

## 3. Finite prefixes, errors and the current receipt event

`run` has a genuine one-step recurrence, proved by `run_succ`:

```lean
run dispatch delay world (n + 1) =
  (step dispatch delay (run dispatch delay world n)).getD
    (run dispatch delay world n)
```

The initial state is Force, the next state is the opened Name, and the
following state is the computed success or failure of `evaluate`.
`every_prefix` exhausts these cases. Terminal states stutter: `fuel` in the
raw observation is an observation budget, not a claim that each larger
number performs another native transition. In particular `finish` appends
one receipt once; larger budgets observe the same terminal projected world.
No bound truncates the set of finite observations, and no successful result
is needed to construct this graph.

The outcome order follows the native selected branch:

| Condition, in evaluation order | Model outcome | Native interpretation |
| --- | --- | --- |
| No lexical binding | `missingBinding` | `MissingBinding`. |
| Cell address outside the vector | `invalidAddress` | Native direct-index panic boundary, not a new normal `RuntimeUnavailable`. |
| In-range cell not initialized | `uninitializedBinding` | `UninitializedBinding` for this lexical case. |
| Dispatch call fails | `dispatch code` | The externally read native dispatch error; error-label decoding remains external. |
| View address outside the vector | `invalidViewAddress` | Native direct-index panic boundary in `matches_value`. |
| In-range abstract view slot absent | `missingViewSnapshot` | Malformed `Store` projection; an actual `Vec<View>` cannot have this hole. This is not called a normal native error. |
| Present view has another value | `invalidView` | `InvalidSourceReference`. |
| Present matching view | `returned address raw` | Append the actual Name receipt and Observe-to-Return. |

The successful generic theorem requires both the cell bound and the view
bound. The old `CaptureAt.Matches` only witnesses the abstract view cell; it
does not prove that the address is within the native vector. Neither bound
is inferred from semantic membership. Explicit failure lemmas cover every
branch above; `failed_prefix` retains the pre-receipt projected world.

`failed_observation` proves that a failed prefix is still in `force`, that
its form is `unfinished`, and that its concrete observation guards are
invalid. The original `TraceForm` has only `pureReturn` and `unfinished`;
representing failure by the latter alone would be insufficient. The false
phase guard prevents a failed prefix from being certified as a safe
unfinished one. Failures are retained, not filtered by a guard or membership.

`eventAt` uses the computed current world. The actual current residual
configuration and evidence fields are supplied separately for each prefix;
they are not identified with the creation configuration. At zero it returns
the exact demand event. `prefix_event` proves equality with the frozen
Carrier event constructor, and `prefix_form` uses that same event in the
Return tuple. The selected descriptor is
`demand.eta.views.descriptor capture.address capture.raw.view`, not a new
existential descriptor chosen after the result.

`return_receipt` proves the record at the old receipt length, increment by
one, and preservation of the views and cells. The receipt retains the actual
current invocation owner and the Name occurrence. The caller's later
Value-entry receipt or body return is not substituted for this event.

## 4. Constructed extraction and remaining independent evidence

Every `Independent` record keeps the following premises visible:

- the selected raw dispatch result and actual cell/view bounds;
- compatibility, event coherence and the existing world guards at every
  computed prefix;
- every unchanged primitive observation guard at the same raw observation;
- the original `WorldFields` projection of the unchanged positive fields.

It contains no successful Force premise, raw prefix equation, trace-form
conclusion, incidence conclusion, returned member, trace `Meaning`,
whole-carrier `Meaning` or `NativeExtraction`. `Independent.execution`
constructs the execution readout and transports its independent fields
along the proved prefix-event equality. `Independent.observationAt`
computes all operational members of the original record. `everyObservation`
extracts the budget from the actual tag and proves that it is the same raw
observation; it does not choose an unrelated existential event or result.

`nativeExtraction` retains exactly the same original Carrier row, interface,
Delay, `History.capture`, demand and raw observation. Its remaining global
registration premise quantifies over **every** `Reach` event and every
original admitted demand. `Reach` is the unchanged closure of the original
compatibility relation. Registration therefore cannot exclude a difficult
lawful future by selecting a smaller future relation.

The independent `History` still supplies allocation, the same initialized
capture, environment persistence, stable raw cell and view assignment,
original inert guards, capture projections, and surrounding worlds. In
particular its `worlds` field contains original world `Meaning`. This is an
unclosed independent semantic owner; it must not be filled by using the
very carrier meaning being introduced. The module neither constructs that
history circularly nor infers any `Background` row from `Meaning`.
`WorldFields` remains the existing explicit projection syntax, not a proof
that every arbitrary positive formula has such a projection.

With those same independent owners, the final application is:

```lean
name_delay_from_native_prefixes
  base native references row delay history registered evidence :
  Meaning (OriginalParameterSemantics.inputs (inputs base native) references)
    (.carrier row)
```

The proof constructs `nativeExtraction ...` and passes it directly to the
frozen `OriginalIdentityCarrier.name_delay_whole`. There is no separate
replacement definition of carrier acceptance or original descriptor meaning.

## 5. Actual allocated-and-bound constructor application

`allocated_bound_force` is an operational application without a surrounding
world membership premise. It starts with an actual `bindEvent`, using any
existing parent lexical environment, and the frozen fresh Delay allocation
whose saved environment is that new binding environment. The assumptions are
the actual parent node readback, matching in-range raw view, selected
contract/event fields, native carrier/executable/mode readbacks, and the
native `dispatch = noDictionaries` branch.

It then derives, for every budget `n + 2`:

```lean
let demand := bindEvent before parent name raw node found descriptor fields
let delay := NameDelay.mk handle before.current.world.environments.size name site
let observation := observe native input demand delay (n + 2)
(inputs base native).force input demand observation ∧
(inputs base native).traceForm (observation.atInterface interface) =
  .pureReturn ⟨descriptor, before.eta.views.value raw.value,
    before.eta.views.root raw.value, observation.event⟩
```

There is no assumed successful Force, initialized lookup, cell-bound, raw
prefix or Return form in this theorem. `capturedByBind` computes the first
three, the allocated code gives `owner`, and the interpreter supplies Force
and Return. The new cell's descriptor is installed by the existing
`installValueContract`; it is not guessed from the raw value's shape.
The raw value remains arbitrary and may itself contain a callable or
computation. Name/Observe does not execute that latent value.

This pair has the operational shapes needed by `EntryFacts.executed` and
`EntryFacts.actualReturn`. Assembling an existing
`OriginalIdentityRealization.Use`/receipt packet from this computed raw
observation, and proving all remaining `EntryFacts` fields at its same
post-Force pre-bind world, remains an explicit join. This module does not
claim to have removed every entry premise of
`generated_identity_from_name_delay`.

## 6. Native state boundary and remaining owners

`SourceIdentityWorld.World` is a projection, not the complete Rust machine.
Its frozen header explicitly excludes the separate dictionary-machine store.
`Native.dispatch` returns only `Except Nat (Option Nat)`; it does not return a
poststate. In the native implementation `dispatch::Machine::name`
(`dispatch.rs:161`) can append context words and substitutions, reserve
storage, call `then`, and fail after a partial mutation. A later view mismatch
can also occur after dispatch succeeded. This module does not simulate those
stores, counters or partial mutations.

Consequently the `Rest` component used for authentic extraction must contain
only fields unchanged by this selected projected action. The dictionary
store, mutable dispatch counters and `operation_v1_trace` bookkeeping at
`machine.rs:815` cannot be silently placed in a supposedly unchanged `Rest`.
Their actual current state may be carried in the independently supplied
`EventReadout.residual`/event-evidence readouts, but the equations producing
those readouts from Rust have not been proved here. On an error after
dispatch, preservation of those unprojected mutations is likewise external;
`failed_prefix` claims preservation only of the represented world fields.
Even the dictionary-free theorem still leaves optional trace bookkeeping and
scheduler/frame state at that current-readout boundary.

The first remaining owners are:

1. **Authentic native projection.** Extract carrier/handle identity, executable
   allocation, exact resolved instruction mode, lexical binder/site encoding,
   valid native environment arena and store projections, and current residual
   and event fields. The frozen `NativeClosureEnvironment` lookup corresponds
   to the native parent walk under its `Valid` condition; the constructor
   equations alone do not prove arbitrary malformed arenas valid.
2. **Dictionary-present transitions.** Compute the raw result/error and the
   complete dispatch poststate, including partial failure and instrumentation,
   then prove the current event readout. The successful Name projection is
   proved conditional on the raw dispatch result, not on a full dispatch-state
   simulation.
3. **Same owner through all demands.** Derive the `registered` premise from
   native executable persistence and source resolution at every original
   compatible future, without narrowing `Reach`, `demand` or admission.
4. **Independent worlds and guard fields.** Supply `History` and the primitive
   guard/field evidence from the original world and source rules. Immutable
   raw identity and `CarrierAccepted` alone do not supply these meanings.
5. **Actual entry packet and other constructors.** Join the computed Force and
   Return to the existing same-event `Use` packet and its remaining entry
   facts; retain the ordinary obligations for non-Name, effectful, suspended,
   divergent and other lawful external carriers. The full source constructor
   induction and full original soundness/Effect theorem remain open.

## 7. Verification and complete axiom audit

The project pins Lean `4.35.0` (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
Lake `5.0.0-src+eb6cafb`, no external packages, and proof-process options
`-j1 -M1024`. The resolved executable was
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
All direct calls used the project directory, no `-o`, and a 120-second cap.
Only the parent wrote build artifacts.

Final direct source check:

```text
lake env lean -j1 -M1024 YulangClosure/OriginalNameForceExtraction.lean
exit 0; 2.618 seconds; zero diagnostics
/tmp/yulang-name-force-extraction/check-07.json
/tmp/yulang-name-force-extraction/check-07.log
```

The parent then built this exact frozen source together with
`OriginalBoundWorkExecution`: 42 jobs, exit 0, zero diagnostics.
The log is `/tmp/yulang-name-bound-work-build.log`, SHA-256
`1ea5c169bb15bf04070a2d857b592163e61829bcd4f0b268701ec0dbc84e859e`.
This is a focused build receipt, not a leaf claim of a fresh default build.

The all-origin audit imported that actual parent-built target and selected
constants by their defining module index. It covers private/generated
constants as well as authored public names, prints their complete types and
transitive axioms, and separately checks every authored theorem root.

```text
lake env lean -j1 -M2048 /tmp/yulang-name-force-extraction/Audit.lean
exit 0; 2.276 seconds; zero diagnostics and zero type elisions
409 originating declarations; 189 theorem constants; 31 authored theorem roots
```

The 2 GiB cap was used only for the full type/axiom census, as authorized;
source proofs remained at the project's 1 GiB cap. The declaration kinds are
176 definitions, 189 theorem constants, 9 inductives, 26 constructors and
9 recursors. No originating axiom declaration exists.

| Transitive axiom set | All 409 declarations | All 189 theorem constants | 31 authored theorems |
| --- | ---: | ---: | ---: |
| none | 289 | 108 | 1 |
| `propext` | 104 | 69 | 24 |
| `propext`, `Quot.sound` | 16 | 12 | 6 |

`Classical.choice` is unused. No extra axiom, `sorryAx`, unchecked native
proof or checker bypass occurs. The exact authored grouping is:

- No axioms: `every_prefix`.
- `propext`, `Quot.sound`: `owner_from_allocation`, `project_run`,
  `prefix_event`, `prefix_result`, `name_delay_from_native_prefixes`,
  `allocated_bound_force`.
- `propext`: `run_succ`, `failed_prefix`, `missing_binding`,
  `uninitialized_binding`, `dispatch_failure`, `initialized_evaluate`,
  `dangling_address`, `other_force_unchanged`, `other_incidence_unchanged`,
  `checked_domain_unchanged`, `actual_admission_unchanged`,
  `prior_observation_unchanged`, `other_owners_unchanged`,
  `every_owned_prefix`, `force_incidence`, `prefix_valid`, `prefix_form`,
  `failed_observation`, `return_receipt`, `dangling_view`, `missing_view`,
  `mismatched_view`, `captured_by_bind_bound`, `bound_name_evaluate`.

All 409 exact types and axiom lists are in
`/tmp/yulang-name-force-extraction/census.json`; the root list and origin
selector are in `audit-manifest.json`. Audit source SHA-256:
`3e941f75cacad3ac9879dc09ee84b663ac5632090d46f2ca83e56727e7c812c1`.
Audit log `audit-01.log` SHA-256:
`d519cf23de78c06d0fda606b8abd6f780a8f73288625dadc89bc1555d68e4b89`.
Actual exit metadata are in `audit-01.json`, with grouped totals in
`audit-summary.json`.

Seven proof calls and one of the two permitted audit calls were used.
Failed proof calls 1–3 and 5 retain their actual logs: they concerned local
`Except`/`Option` reduction, dependent projection equality, receipt-list
normalization and the order of simplification at the bound Return theorem.
Checks 4 and 6 passed their earlier snapshots. Check 7 added the explicit
view-address distinction/bound and interface-preservation equalities and
passed the final frozen proof. No resource increase or admitted hole repaired
those proof failures.

## 8. Input pins and stopped-write scope

The initial six input hashes were rechecked unchanged before note freeze.
The complete source/native/manuscript/toolchain manifest is
`/tmp/yulang-name-force-extraction/final-input-manifest.json`.

| Input | SHA-256 |
| --- | --- |
| `OriginalIdentityCarrier.lean` | `f26878514518f14a4a99e799dad2ca28e4513c467a8dd24d86e6329b9e640616` |
| `OriginalIdentityRealization.lean` | `30b0676f4af22dc7da2c75596a338db57a24b17662a4057801cfdff7ab4a2f42` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `OriginalParameterSemantics.lean` | `733c5b05e0db226f95d14ff2161c46e9a389b43d86b365b000a9656ec4fd0bd2` |
| `SourceIdentityWorld.lean` | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` |
| `machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |
| `dispatch.rs` | `f45057373f2ed3a7b6ce915611db093015fb93cdb05984a5e3b23cfd44720873` |

Only this paired note, `OriginalNameForceExtraction.lean`, and the assigned
`/tmp/yulang-name-force-extraction/` directory were written. Frozen prior
proofs, notes and reviews, Rust, import roots, shared status, Git and build
caches were untouched. The final receipt records exact source/note/log hashes
and the stopped-write timestamp; independent review and integration remain
with the parent.
