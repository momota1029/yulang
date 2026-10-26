# Paper allocation/execution bridge — frozen producer handoff

Status: **CHECKER-ACCEPTED, pending independent review**. This closes the stated
finite allocation/execution bridge for the represented paper judgments. It does
not close original whole-language safety, source `rec`, inference A/B, progress,
guardedness, full-owner resumption, or source/native correspondence.

Baseline supplied by the primary: `adfed0dbcc8875ac0c9e66c40a0b967b3e9df073` on
`momota1029/yulang`, branch `yulang3`. Producer: generic bounded `lean_prover`
fallback, `/root/paper_allocation_execution`. No descendants or Git operations.

## Frozen output and leases

- Proof: `notes/theory/lean/YulangClosure/PaperAllocationExecution.lean`.
- Proof SHA-256: `d5cd9f4499ec0c6e67e73a9444634671e43b507368c418b1d9ecec7fd57f0aa4`.
- This handoff is the only other repository write.
- Scratch/cache: `/workspace/scratch/f98087c7ac1a/paper-allocation/` only.
- No existing Lean module, root import, manifest, toolchain, compiler source,
  expectation, shared scheduling record, or R63-owned file was edited.
- The isolated checked source bytes equal the repository bytes for all 22
  modules in this module's import closure, including the new module.

## Assessed gap and original source map

R29 `FreshHeap.finite_allocation` proves exact fresh payload allocation but has
no current executor state or saved-request history. R59 observations use a fixed
heap. R61 `PaperExtendedExecution.finite_interaction` fixes one graph throughout.
R62 `allocated_force_control` assumes state typing in the already extended graph.
The new bridge derives that transport and subsequent state/saved typing from
initial typing and source-directed allocation premises.

| Governing source | Actual clauses consumed | New declarations / boundary |
| --- | --- | --- |
| `docs/yulang-operational-type-safety-ja.tex`, lines 264–269 | Immutable finite heap; reference typing; full heap judgment also includes guard | `HeapLookupPreserved`, observation transport, `history_extension`; only existing `HeapPayloadTyped`, not the guarded manuscript heap judgment |
| Same, lines 324–326 and 980–990 | Fresh simultaneous rec allocation; old nodes unchanged; same substitution in RHSs and body | `allocation_body`, `allocated_body_history`; no new rule for `Computation.recursive`, no proof of source-formal ordering or guard |
| Same, lines 458–466 | Saved continuation body retained across multiple responses | `SavedRequest`, `saved_response_prefix`, `saved_response_history`; represented empty-owner case only |
| Same, lines 1140–1161 | Finite internal/external prefix, fresh response heap extension, original continuation re-use | `finite_history`, `interaction_history`, `saved_response_history`; preservation component, not progress or Bad exclusion |
| `notes/theory/2026-10-24-corrected-core-value-continuation.md`, §§2,4–6 | V1(d), V4 request/continuation introduction, V5(2,6,8), V6 current response and unchanged saved body | Existing actual typing/step lemmas are consumed; no safety law is supplied by a history constructor |
| `notes/theory/2026-10-24-corrected-machine-simulation.md`, §4.2 | Immutable saved evidence is distinct from current world; no saved world restoration | Saved packet contains operation, payload, binder and body only; reentry uses the current graph/heap. This is no proof of owner/activity/release world simulation |
| `docs/yulang-whole-proof-closure-ja.md`, §§1,3 | Original whole source, execution and native obligations remain separate | Whole theorem remains OPEN with its original scope |

Source hashes:

| Source | SHA-256 |
| --- | --- |
| Operational manuscript | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| Corrected core value/continuation note | `4d8ffd63cbb65cd6917145fa31a4cb3f04656a19f7b71fd0e3fdd6cecaabfbeb` |
| Corrected machine simulation note | `fffb4f1540739020a0702d4f7b07d41cd9b68a9063f36d24292914b84e6b606d` |
| Whole-proof closure document | `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |

The opening manuscript correction notice and corrected current-world boundary
were read. These research manuscripts do not authorize new compiler semantics.

## Exact construction and assumptions

All public names below have prefix
`YulangClosure.PaperTypes.PaperAllocationExecution.`. Their complete printed
types and axiom results are retained in the appendix.

`History d binder e initialGraph initialHeap initialState g heap state saved`
is finite **evidence around the actual `PaperCoreControl.State`**. Its indices
retain literal graph, heap, state and saved packet witnesses. It has six cases:

1. `initial`: same graph, heap and state, empty saved list.
2. `internal`: actual `PaperExtendedExecution.controlStep ... = some next`.
3. `allocation`: actual `formals block ++ g` and `allocate block rho heap`, with
   unique block IDs, freshness against the current graph and heap, current-graph
   `TermSubstitutionTyped d g source e rho`, and `BlockTyped d g source block`.
   It leaves actual executor syntax and all saved packets unchanged.
4. `save`: records the exact currently exposed empty-owner request; executor
   state is unchanged. No saved/request/body typing is a constructor premise.
5. `response`: starts at that exact exposed request and uses its actual
   `operation.responseType`, checked under **current** `g` and `e`. The actual
   response function equation is proved by `saved_response_eq`. The complete
   request is recorded, retaining operation instance, payload, binder and body.
6. `observedForce`: a supplied finite R59 observation on the **current heap**
   reaches `delay body`, followed by the existing real Force/Delay transition.
   Its state preservation uses R62 and R61; finite observation is not asserted
   to be a `controlStep` or to exist for every value.

No constructor contains final state typing, final heap typing, saved continuation
typing, a preservation law, or safety. The main induction consumes
`FreshHeap.finite_allocation` and `PaperExtendedExecution.preservation` directly.

### Main results

- `observationStep_transport` / `observationTrace_transport` preserve exact
  source/target values under successful immutable lookup preservation.
  `allocation_observationStep` / `allocation_observationTrace` instantiate this
  for the real allocator using actual heap freshness, without typing premises.
- `allocation_body` starts with source `BlockTyped`, typed simultaneous
  substitution, source body typing in `formals.map snd ++ source`, initial heap
  payload typing and an initial typed let stack. It derives the real public
  substitution success, allocated heap typing and allocated state typing with
  the same stack/result. It never assumes typing in the extended graph.
- `interaction_history` embeds every existing R61 interaction segment and its
  actual protocol into a history, retaining every earlier saved packet.
- `history_extension` derives old successful graph/heap lookup preservation and
  an exact old-heap suffix from the history. `history_preservation` uses only
  initial state/heap typing and independent `BodiesTyped d`, in addition to the
  actual history's source/protocol premises, to derive current heap, current
  state and **all** saved-request typing at the same result type.
- `finite_history` additionally derives erased current computation typing and,
  for every saved packet, payload typing at its actual payload field and saved
  continuation typing at its actual response field and the shared final result.
- `saved_response_prefix` starts a separate invocation at the actual saved
  request's real response interface under the current graph, then preserves an
  actual R61 executor trace. It does not invent a scheduler jump from an
  arbitrary current state to a saved request.
- `saved_response_history` permits further allocation, execution, response and
  Force observation after that invocation. It derives final heap/state typing,
  types **both** original and newly saved packets at the final graph, and keeps
  the original packet's body/binder/operation unchanged. It can be applied to
  the same packet repeatedly; no save-time graph or heap is restored.
- `allocated_body_history` composes the source allocation/body entry directly
  with the full history theorem. Its initial allocated state and all final
  graph/heap/state/saved typing are conclusions, not input certificates.

### Non-vacuous current-graph/replay discriminator

`fresh_response_replay` constructs every step and source/protocol obligation:

1. Begin with a syntactically typed exposed request and empty graph/heap. Its
   saved body is exactly `force (variable 0)`, response type `thunk Bool` and
   final result `Bool`; payload is Unit.
2. Save that packet, allocate node 10 holding `delay (return true)`, and respond
   with the newly available `graphReference 10`.
3. Perform actual empty-owner substitution, allocate node 20 holding
   `delay (return false)`, then observe the unchanged old node 10 and execute
   Force/Delay to return `true`.
4. Invoke the **same saved body** with current node 20, execute actual response
   substitution and current-heap observation/Force to return `false`.

No future step, final typing, or final graph extension is assumed in this
example. `example_response_requires_extension` proves node 20 cannot be typed
as the response in the empty save-time graph but is typed in the current graph.
This is a closed explicit-paper discriminator; it does not claim frontend
elaboration of a whole source program.

## Verification receipt

Pinned project files were read: `leanprover/lean4:v4.35.0`, no external packages,
`moreLeanArgs = ["-j1", "-M1024"]`. Resolved native executable:

`/workspace/scratch/e41512dd7957/toolchains/lean-4.35.0-linux/bin/lake`.

Actual versions, both exit 0:

```text
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
Lean (version 4.35.0, x86_64-unknown-linux-gnu,
      commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Verification owner: this leaf, isolated project
`/workspace/scratch/f98087c7ac1a/paper-allocation/project`.
An old read-only cache was copied into that project, then every module in the
actual dependency order was checked/built against the copied baseline sources.
The 21 dependencies were processed serially before the new module, so no
dependency's changed inputs were hidden by direct `lake env` checking.

Commands used, with `LEAN_NUM_THREADS=1`, one Lean process at a time and a
120-second timeout per focused invocation:

```text
lake --no-cache build +MODULE             # each dependency, topological order
lake --no-cache env lean -j1 -M1024 YulangClosure/PaperAllocationExecution.lean
lake --no-cache -q build +YulangClosure.PaperAllocationExecution
lake --no-cache env lean -j1 -M1024 AuditPaperAllocation.lean
```

The final module build exited 0 in 1.523 seconds. The complete audit exited 0 in
1.139 seconds. The audit enumerates theorem constants by actual originating
module, including generated declarations, validates all 24 required public
roots, prints every exact type, prints every transitive axiom list and rejects
nonstandard axioms. It is adapted from the committed `AuditExecutionProofs.lean`.
It additionally prints `History` and the three typing/lookup predicate
definitions, so constructor premises are reviewable rather than hidden.

Final result: **50/50 theorem constants audited**: 24 public source theorems and
26 generated theorems. Axiom totals are 40 `[propext, Quot.sound]`, 3 `[propext]`,
7 `[]`. No `sorryAx`, project axiom, `Classical.choice`, native-evaluation axiom
or other dependency appears. All public theorems except `saved_response_eq`
and `example_packet_typed` have `[propext, Quot.sound]`; those two have
`[propext]`. Source scanning across all 22 imported modules found no `sorry`,
`admit`, `axiom`, `skipKernelTC` or `native_decide` token.

No warnings originate in the new module. Final build replayed 658 warnings in
unchanged, unleased dependencies: `PaperExecutionSyntax` 23,
`PaperExecutionBinderLaws` 235, `PaperTermSubstitution` 96, `PaperCoreStep` 4,
`PaperTypeBetaExecution` 276, `PaperTupleSplitExecution` 22 and
`PaperPerformLetExecution` 2. These are existing unused-variable/simp-argument
and deprecated-name diagnostics. Their owning files remain with the primary;
no unrelated warning repair was attempted under this lease.

Material failed checks and repairs were preserved: the first module build
failed dependent elimination on a projected saved operation field; destructing
the actual record before request inversion repaired it. One intermediate
check used reserved identifier `prefix`; it was renamed. The concrete resume
proof needed explicit unfolding of `SavedRequest.resume` and the actual partial
substitution, rather than a failed bare rewrite/`rfl`. One unused `Bool.true_eq`
simp argument was removed. No failure was repaired by a new hypothesis, hole,
weakened theorem, changed semantics or resource increase.

### Exact evidence paths and hashes

All following paths are under `/workspace/scratch/f98087c7ac1a/paper-allocation/`:

| Evidence | SHA-256 |
| --- | --- |
| `complete-audit.log` (all 50 exact types/axioms and predicate definitions) | `06da09ea0af9ca80ee351bb3a9cfea1dd8c9969b7b9c6036665f89184221c9a0` |
| `public-audit.log` (24 exact public types/axioms, reproduced below) | `9a9fa924bbe42c02d576c9e0a4887714cd2f0c98d807f7f1968226d9acdb493c` |
| `input-hashes.json` (22 repository/isolated source pairs, byte-equal) | `f1c4968769dffd28811b00fc0ea5bcbe46adc063c2e9336b6076f9a68a1362fb` |
| `final-build.log` (complete final build output) | `5744d75ce15b3ec62787f7f20fb29ae022234aa2ac0b137e2df4e18df7cc18d2` |
| `project/AuditPaperAllocation.lean` (all-theorem audit source) | `bf71818e43050d8679c86a41ea0a97cdb714b6b6122b634fc5b5f92b311089b1` |
| `axioms.json` (complete 50-name axiom inventory) | `18e9346382ace1d552adb1a67c57a7768bcb61c5b7f2d9ef1b2bb477effc7878` |

Also retained: `check_serial.py`, `dependency-order.txt`, `theorems.txt`,
`build-00.log` through `build-21.log`, `focused-02.log` through
`focused-05.log`, and isolated project/cache outputs. `build-21.log` preserves
the initial failed module build; `focused-03.log`/`focused-04.log` preserve the
concrete resume proof's failures. Direct tool diagnostics also recorded the
reserved-identifier repair. The final direct check `focused-05.log` was clean
before adding the final extension discriminator, which was then built and
audited in the final successful module build.

## Remaining premises, parent application and ownership

The represented bridge no longer needs final-graph state typing or an external
saved-continuation preservation assumption. Initial `HeapPayloadTyped` and
`StateTyped`, independently checked finite table bodies, source-directed block
and substitution typing for each actual allocation, actual unique/fresh IDs,
actual successful executor transitions, current-instance typed foreign
responses, and supplied finite observations are its precise inputs.

The original parent remains OPEN. Its next source/semantics owners must supply:

1. The correspondence from original `rec` bindings and source order to the
   explicit de Bruijn block/body substitution. `PaperComputationTyped` still
   has no represented `recursive` typing case, and the executor still has no
   source-rec step. `allocation_body` is a usable component, not that missing
   constructor correspondence. Owner: source/execution proof lane.
2. Guarded heap construction and constructor-observation existence/termination.
   `HeapPayloadTyped` admits self-alias loops; no progress result is inferred.
   Owner: guarded graph/canonical-form proof lane.
3. Full nonempty-owner, seven-frame and corrected current-world reentry, with
   lifetime, release and source evidence identity. Empty owners make freshening
   vacuous here; saved packet availability is not a lifetime theorem. Owner:
   corrected control/source correspondence lane.
4. All remaining original source constructors, native implementation agreement,
   inference soundness/principal coverage/naturalness/termination, precise effect
   inclusion and whole-source safety. Their original domains/quantifiers are
   unchanged. Owners remain the existing parent gates.

The primary can integrate the new module into its root/audit import surfaces
after independent review. Those paths were not leased to this producer, and a
default build without that import would not itself cover the new module.

## Writes-stopped receipt

Source and this handoff are frozen for review. All launched Lean/Lake processes
have exited; no checker remains running. No descendants, Git work, compiler
edits, semantic adoption or additional writes are pending. The bounded packet
completed within its 45-minute envelope; precise aggregate agent active time
was not instrumented and is not claimed. The longest observed serial dependency
build was 11.68 seconds. This producer's check is not independent review.

## Appendix: complete public theorem type and axiom audit

The following is the unchanged public projection of the complete 50-declaration
audit. The complete generated-theorem inventory follows it.

```text
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_history
@YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_history : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {binder : YulangClosure.PaperTypes.TermName}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {initialGraph : YulangClosure.PaperTypes.GraphEnvironment}
  {initialHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {initialState : YulangClosure.PaperTypes.PaperCoreControl.State} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {state : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {result : YulangClosure.PaperTypes.Ty}
  {packet : YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {response : YulangClosure.PaperTypes.Value}
  {finalGraph : YulangClosure.PaperTypes.GraphEnvironment} {finalHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {last : YulangClosure.PaperTypes.PaperCoreControl.State}
  {newSaved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest},
  YulangClosure.PaperTypes.PaperTemplateExecution.BodiesTyped d →
    YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d initialGraph e initialHeap →
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped d initialGraph e initialState result →
        ∀
          (history :
            YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g
              heap state saved),
          packet ∈ saved →
            YulangClosure.PaperTypes.PaperValueTyped d g e response packet.operation.responseType →
              ∀
                (branch :
                  YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e g heap (packet.resume response)
                    finalGraph finalHeap last newSaved),
                YulangClosure.PaperTypes.PaperExtendedExecution.responseStep response packet.state =
                    Option.some (packet.resume response) ∧
                  YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d finalGraph e finalHeap ∧
                    YulangClosure.PaperTypes.PaperCoreControl.StateTyped d finalGraph e last result ∧
                      YulangClosure.PaperTypes.PaperComputationTyped d finalGraph e
                          (YulangClosure.PaperTypes.PaperCoreControl.erase last) result ∧
                        YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestsTyped d finalGraph e
                            (newSaved ++ saved) result ∧
                          YulangClosure.PaperTypes.PaperContinuationTyped d finalGraph e
                            (YulangClosure.PaperTypes.Value.continuation [] packet.responseBinder packet.body)
                            packet.operation.responseType result
'YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_history' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_history

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_eq
YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_eq : ∀
  (saved : YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest) (response : YulangClosure.PaperTypes.Value),
  YulangClosure.PaperTypes.PaperExtendedExecution.responseStep response saved.state =
    Option.some (saved.resume response)
'YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_eq' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_eq

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.example_resume_step
YulangClosure.PaperTypes.PaperAllocationExecution.example_resume_step : ∀ (binder : YulangClosure.PaperTypes.TermName)
  (identity : Nat),
  YulangClosure.PaperTypes.PaperExtendedExecution.controlStep
      YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable binder
      ((YulangClosure.PaperTypes.PaperAllocationExecution.examplePacket binder).resume
        (YulangClosure.PaperTypes.Value.graphReference identity)) =
    Option.some
      { head := YulangClosure.PaperTypes.Computation.force (YulangClosure.PaperTypes.Value.graphReference identity),
        stack := [] }
'YulangClosure.PaperTypes.PaperAllocationExecution.example_resume_step' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.example_resume_step

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.example_block_typed
YulangClosure.PaperTypes.PaperAllocationExecution.example_block_typed : ∀
  (d : YulangClosure.PaperTypes.DeclarationTable) (g : YulangClosure.PaperTypes.GraphEnvironment)
  (e : YulangClosure.PaperTypes.TypeEnvironment) (identity : Nat) (value : Bool),
  YulangClosure.PaperTypes.FreshHeap.BlockTyped d g e
    (YulangClosure.PaperTypes.PaperAllocationExecution.exampleBlock identity value)
'YulangClosure.PaperTypes.PaperAllocationExecution.example_block_typed' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.example_block_typed

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationStep
@YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationStep : ∀
  {block : YulangClosure.PaperTypes.FreshHeap.Block} {rho : Nat → YulangClosure.PaperTypes.Value}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {source target : YulangClosure.PaperTypes.Value},
  (∀ (r : Nat), r ∈ YulangClosure.PaperTypes.FreshHeap.ids block → ¬r ∈ List.map Prod.fst heap) →
    YulangClosure.PaperTypes.PaperHeapObservation.ObservationStep heap source target →
      YulangClosure.PaperTypes.PaperHeapObservation.ObservationStep
        (YulangClosure.PaperTypes.FreshHeap.allocate block rho heap) source target
'YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationStep' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationStep

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.state_graphWeaken
@YulangClosure.PaperTypes.PaperAllocationExecution.state_graphWeaken : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {old new : YulangClosure.PaperTypes.GraphEnvironment} {e : YulangClosure.PaperTypes.TypeEnvironment}
  {state : YulangClosure.PaperTypes.PaperCoreControl.State} {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.GraphLookupPreserved old new →
    YulangClosure.PaperTypes.PaperCoreControl.StateTyped d old e state result →
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped d new e state result
'YulangClosure.PaperTypes.PaperAllocationExecution.state_graphWeaken' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.state_graphWeaken

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.history_observation_transport
@YulangClosure.PaperTypes.PaperAllocationExecution.history_observation_transport : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {binder : YulangClosure.PaperTypes.TermName}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {initialGraph : YulangClosure.PaperTypes.GraphEnvironment}
  {initialHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {initialState : YulangClosure.PaperTypes.PaperCoreControl.State} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {state : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest}
  {source target : YulangClosure.PaperTypes.Value}
  (history :
    YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g heap
      state saved),
  YulangClosure.PaperTypes.PaperHeapObservation.ObservationTrace initialHeap source target →
    YulangClosure.PaperTypes.PaperHeapObservation.ObservationTrace heap source target
'YulangClosure.PaperTypes.PaperAllocationExecution.history_observation_transport' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.history_observation_transport

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.history_preservation
@YulangClosure.PaperTypes.PaperAllocationExecution.history_preservation : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {binder : YulangClosure.PaperTypes.TermName}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {initialGraph : YulangClosure.PaperTypes.GraphEnvironment}
  {initialHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {initialState : YulangClosure.PaperTypes.PaperCoreControl.State} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {state : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperTemplateExecution.BodiesTyped d →
    YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d initialGraph e initialHeap →
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped d initialGraph e initialState result →
        ∀
          (history :
            YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g
              heap state saved),
          YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d g e heap ∧
            YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e state result ∧
              YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestsTyped d g e saved result
'YulangClosure.PaperTypes.PaperAllocationExecution.history_preservation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.history_preservation

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.interaction_history
@YulangClosure.PaperTypes.PaperAllocationExecution.interaction_history : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {binder : YulangClosure.PaperTypes.TermName}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {initialGraph : YulangClosure.PaperTypes.GraphEnvironment}
  {initialHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {initialState : YulangClosure.PaperTypes.PaperCoreControl.State} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {first last : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest}
  (start :
    YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g heap
      first saved)
  (path : YulangClosure.PaperTypes.PaperExtendedExecution.InteractionTrace d binder first last),
  YulangClosure.PaperTypes.PaperExtendedExecution.ProtocolTyped g e path →
    ∃ retained,
      Nonempty
          (YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g
            heap last retained) ∧
        ∀ (packet : YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest), packet ∈ saved → packet ∈ retained
'YulangClosure.PaperTypes.PaperAllocationExecution.interaction_history' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.interaction_history

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.example_packet_typed
YulangClosure.PaperTypes.PaperAllocationExecution.example_packet_typed : ∀ (binder : YulangClosure.PaperTypes.TermName),
  YulangClosure.PaperTypes.PaperCoreControl.StateTyped YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable []
    [] (YulangClosure.PaperTypes.PaperAllocationExecution.examplePacket binder).state
    (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.bool)
'YulangClosure.PaperTypes.PaperAllocationExecution.example_packet_typed' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.example_packet_typed

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.saved_requests_graphWeaken
@YulangClosure.PaperTypes.PaperAllocationExecution.saved_requests_graphWeaken : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {old new : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.GraphLookupPreserved old new →
    YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestsTyped d old e saved result →
      YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestsTyped d new e saved result
'YulangClosure.PaperTypes.PaperAllocationExecution.saved_requests_graphWeaken' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.saved_requests_graphWeaken

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_prefix
@YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_prefix : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {binder : YulangClosure.PaperTypes.TermName}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {initialGraph : YulangClosure.PaperTypes.GraphEnvironment}
  {initialHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {initialState : YulangClosure.PaperTypes.PaperCoreControl.State} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {state : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {result : YulangClosure.PaperTypes.Ty}
  {packet : YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {response : YulangClosure.PaperTypes.Value}
  {last : YulangClosure.PaperTypes.PaperCoreControl.State},
  YulangClosure.PaperTypes.PaperTemplateExecution.BodiesTyped d →
    YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d initialGraph e initialHeap →
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped d initialGraph e initialState result →
        ∀
          (history :
            YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g
              heap state saved),
          packet ∈ saved →
            YulangClosure.PaperTypes.PaperValueTyped d g e response packet.operation.responseType →
              YulangClosure.PaperTypes.PaperExtendedExecution.Trace d binder (packet.resume response) last →
                YulangClosure.PaperTypes.PaperExtendedExecution.responseStep response packet.state =
                    Option.some (packet.resume response) ∧
                  YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e last result ∧
                    YulangClosure.PaperTypes.PaperComputationTyped d g e
                        (YulangClosure.PaperTypes.PaperCoreControl.erase last) result ∧
                      YulangClosure.PaperTypes.PaperExtendedExecution.ErasureTrace d binder
                          (YulangClosure.PaperTypes.PaperCoreControl.erase (packet.resume response))
                          (YulangClosure.PaperTypes.PaperCoreControl.erase last) ∧
                        YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestTyped d g e packet result ∧
                          YulangClosure.PaperTypes.PaperContinuationTyped d g e
                            (YulangClosure.PaperTypes.Value.continuation [] packet.responseBinder packet.body)
                            packet.operation.responseType result
'YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_prefix' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_prefix

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.finite_history
@YulangClosure.PaperTypes.PaperAllocationExecution.finite_history : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {binder : YulangClosure.PaperTypes.TermName} {e : YulangClosure.PaperTypes.TypeEnvironment}
  {initialGraph : YulangClosure.PaperTypes.GraphEnvironment} {initialHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {initialState : YulangClosure.PaperTypes.PaperCoreControl.State} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {state : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperTemplateExecution.BodiesTyped d →
    YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d initialGraph e initialHeap →
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped d initialGraph e initialState result →
        ∀
          (history :
            YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g
              heap state saved),
          YulangClosure.PaperTypes.GraphLookupPreserved initialGraph g ∧
            YulangClosure.PaperTypes.PaperAllocationExecution.HeapLookupPreserved initialHeap heap ∧
              (∃ front, heap = front ++ initialHeap) ∧
                YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d g e heap ∧
                  YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e state result ∧
                    YulangClosure.PaperTypes.PaperComputationTyped d g e
                        (YulangClosure.PaperTypes.PaperCoreControl.erase state) result ∧
                      ∀ (packet : YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest),
                        packet ∈ saved →
                          YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestTyped d g e packet result ∧
                            YulangClosure.PaperTypes.PaperValueTyped d g e packet.payload packet.operation.payloadType ∧
                              YulangClosure.PaperTypes.PaperContinuationTyped d g e
                                (YulangClosure.PaperTypes.Value.continuation [] packet.responseBinder packet.body)
                                packet.operation.responseType result
'YulangClosure.PaperTypes.PaperAllocationExecution.finite_history' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.finite_history

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.observationStep_transport
@YulangClosure.PaperTypes.PaperAllocationExecution.observationStep_transport : ∀
  {old new : YulangClosure.PaperTypes.FreshHeap.Heap} {source target : YulangClosure.PaperTypes.Value},
  YulangClosure.PaperTypes.PaperAllocationExecution.HeapLookupPreserved old new →
    YulangClosure.PaperTypes.PaperHeapObservation.ObservationStep old source target →
      YulangClosure.PaperTypes.PaperHeapObservation.ObservationStep new source target
'YulangClosure.PaperTypes.PaperAllocationExecution.observationStep_transport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.observationStep_transport

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationTrace
@YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationTrace : ∀
  {block : YulangClosure.PaperTypes.FreshHeap.Block} {rho : Nat → YulangClosure.PaperTypes.Value}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {source target : YulangClosure.PaperTypes.Value},
  (∀ (r : Nat), r ∈ YulangClosure.PaperTypes.FreshHeap.ids block → ¬r ∈ List.map Prod.fst heap) →
    YulangClosure.PaperTypes.PaperHeapObservation.ObservationTrace heap source target →
      YulangClosure.PaperTypes.PaperHeapObservation.ObservationTrace
        (YulangClosure.PaperTypes.FreshHeap.allocate block rho heap) source target
'YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationTrace' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.allocation_observationTrace

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_typed
@YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_typed : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment}
  {saved : YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {response : YulangClosure.PaperTypes.Value}
  {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestTyped d g e saved result →
    YulangClosure.PaperTypes.PaperValueTyped d g e response saved.operation.responseType →
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e (saved.resume response) result
'YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_typed' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.saved_response_typed

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.observationTrace_transport
@YulangClosure.PaperTypes.PaperAllocationExecution.observationTrace_transport : ∀
  {old new : YulangClosure.PaperTypes.FreshHeap.Heap} {source target : YulangClosure.PaperTypes.Value},
  YulangClosure.PaperTypes.PaperAllocationExecution.HeapLookupPreserved old new →
    YulangClosure.PaperTypes.PaperHeapObservation.ObservationTrace old source target →
      YulangClosure.PaperTypes.PaperHeapObservation.ObservationTrace new source target
'YulangClosure.PaperTypes.PaperAllocationExecution.observationTrace_transport' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.observationTrace_transport

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.saved_request_components
@YulangClosure.PaperTypes.PaperAllocationExecution.saved_request_components : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment}
  {saved : YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest} {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestTyped d g e saved result →
    YulangClosure.PaperTypes.PaperValueTyped d g e saved.payload saved.operation.payloadType ∧
      YulangClosure.PaperTypes.PaperContinuationTyped d g e
        (YulangClosure.PaperTypes.Value.continuation [] saved.responseBinder saved.body) saved.operation.responseType
        result
'YulangClosure.PaperTypes.PaperAllocationExecution.saved_request_components' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.saved_request_components

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.example_response_requires_extension
YulangClosure.PaperTypes.PaperAllocationExecution.example_response_requires_extension : ¬YulangClosure.PaperTypes.PaperValueTyped
      YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable [] []
      (YulangClosure.PaperTypes.Value.graphReference 20)
      (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.bool).thunk ∧
  YulangClosure.PaperTypes.PaperValueTyped YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable
    YulangClosure.PaperTypes.PaperAllocationExecution.exampleGraph [] (YulangClosure.PaperTypes.Value.graphReference 20)
    (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.bool).thunk
'YulangClosure.PaperTypes.PaperAllocationExecution.example_response_requires_extension' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.example_response_requires_extension

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.fresh_response_replay
YulangClosure.PaperTypes.PaperAllocationExecution.fresh_response_replay : ∀
  (binder : YulangClosure.PaperTypes.TermName),
  Nonempty
      (YulangClosure.PaperTypes.PaperAllocationExecution.History
        YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable binder [] [] []
        (YulangClosure.PaperTypes.PaperAllocationExecution.examplePacket binder).state
        YulangClosure.PaperTypes.PaperAllocationExecution.exampleGraph
        YulangClosure.PaperTypes.PaperAllocationExecution.exampleHeap
        {
          head :=
            YulangClosure.PaperTypes.Computation.ret
              (YulangClosure.PaperTypes.Value.literal (YulangClosure.PaperTypes.Literal.boolean Bool.true)),
          stack := [] }
        [YulangClosure.PaperTypes.PaperAllocationExecution.examplePacket binder,
          YulangClosure.PaperTypes.PaperAllocationExecution.examplePacket binder]) ∧
    Nonempty
        (YulangClosure.PaperTypes.PaperAllocationExecution.History
          YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable binder []
          YulangClosure.PaperTypes.PaperAllocationExecution.exampleGraph
          YulangClosure.PaperTypes.PaperAllocationExecution.exampleHeap
          ((YulangClosure.PaperTypes.PaperAllocationExecution.examplePacket binder).resume
            (YulangClosure.PaperTypes.Value.graphReference 20))
          YulangClosure.PaperTypes.PaperAllocationExecution.exampleGraph
          YulangClosure.PaperTypes.PaperAllocationExecution.exampleHeap
          {
            head :=
              YulangClosure.PaperTypes.Computation.ret
                (YulangClosure.PaperTypes.Value.literal (YulangClosure.PaperTypes.Literal.boolean Bool.false)),
            stack := [] }
          []) ∧
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped
          YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable
          YulangClosure.PaperTypes.PaperAllocationExecution.exampleGraph []
          {
            head :=
              YulangClosure.PaperTypes.Computation.ret
                (YulangClosure.PaperTypes.Value.literal (YulangClosure.PaperTypes.Literal.boolean Bool.true)),
            stack := [] }
          (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.bool) ∧
        YulangClosure.PaperTypes.PaperCoreControl.StateTyped
            YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable
            YulangClosure.PaperTypes.PaperAllocationExecution.exampleGraph []
            {
              head :=
                YulangClosure.PaperTypes.Computation.ret
                  (YulangClosure.PaperTypes.Value.literal (YulangClosure.PaperTypes.Literal.boolean Bool.false)),
              stack := [] }
            (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.bool) ∧
          YulangClosure.PaperTypes.PaperContinuationTyped YulangClosure.PaperTypes.PaperAllocationExecution.exampleTable
            YulangClosure.PaperTypes.PaperAllocationExecution.exampleGraph []
            (YulangClosure.PaperTypes.Value.continuation [] binder
              (YulangClosure.PaperTypes.Computation.force (YulangClosure.PaperTypes.Value.variable 0)))
            (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.bool).thunk
            (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.bool)
'YulangClosure.PaperTypes.PaperAllocationExecution.fresh_response_replay' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.fresh_response_replay

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.allocation_body
@YulangClosure.PaperTypes.PaperAllocationExecution.allocation_body : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {old : YulangClosure.PaperTypes.GraphEnvironment} {source e : YulangClosure.PaperTypes.TypeEnvironment}
  {rho : Nat → YulangClosure.PaperTypes.Value} {block : YulangClosure.PaperTypes.FreshHeap.Block}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {body : YulangClosure.PaperTypes.Computation}
  {stack : List YulangClosure.PaperTypes.Computation} {a result : YulangClosure.PaperTypes.Ty},
  (YulangClosure.PaperTypes.FreshHeap.ids block).Nodup →
    (∀ (r : Nat), r ∈ YulangClosure.PaperTypes.FreshHeap.ids block → ¬r ∈ List.map Prod.fst old) →
      (∀ (r : Nat), r ∈ YulangClosure.PaperTypes.FreshHeap.ids block → ¬r ∈ List.map Prod.fst heap) →
        YulangClosure.PaperTypes.TermSubstitutionTyped d old source e rho →
          YulangClosure.PaperTypes.FreshHeap.BlockTyped d old source block →
            YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d old e heap →
              YulangClosure.PaperTypes.PaperComputationTyped d old
                  (List.map Prod.snd (YulangClosure.PaperTypes.FreshHeap.formals block) ++ source) body a →
                YulangClosure.PaperTypes.PaperCoreControl.StackTyped d old e stack a result →
                  YulangClosure.PaperTypes.GraphLookupPreserved old
                      (YulangClosure.PaperTypes.FreshHeap.formals block ++ old) ∧
                    YulangClosure.PaperTypes.PaperAllocationExecution.HeapLookupPreserved heap
                        (YulangClosure.PaperTypes.FreshHeap.allocate block rho heap) ∧
                      YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d
                          (YulangClosure.PaperTypes.FreshHeap.formals block ++ old) e
                          (YulangClosure.PaperTypes.FreshHeap.allocate block rho heap) ∧
                        YulangClosure.PaperTypes.termSubstituteComputation
                              (YulangClosure.PaperTypes.graphFormalReplacements
                                (YulangClosure.PaperTypes.FreshHeap.formals block) rho)
                              body =
                            Option.some
                              (YulangClosure.PaperTypes.replaceTermComputation
                                (YulangClosure.PaperTypes.graphFormalReplacements
                                  (YulangClosure.PaperTypes.FreshHeap.formals block) rho)
                                body) ∧
                          YulangClosure.PaperTypes.PaperCoreControl.StateTyped d
                            (YulangClosure.PaperTypes.FreshHeap.formals block ++ old) e
                            {
                              head :=
                                YulangClosure.PaperTypes.replaceTermComputation
                                  (YulangClosure.PaperTypes.graphFormalReplacements
                                    (YulangClosure.PaperTypes.FreshHeap.formals block) rho)
                                  body,
                              stack := stack }
                            result
'YulangClosure.PaperTypes.PaperAllocationExecution.allocation_body' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.allocation_body

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.stack_graphWeaken
@YulangClosure.PaperTypes.PaperAllocationExecution.stack_graphWeaken : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {old new : YulangClosure.PaperTypes.GraphEnvironment} {e : YulangClosure.PaperTypes.TypeEnvironment}
  {stack : List YulangClosure.PaperTypes.Computation} {a result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.GraphLookupPreserved old new →
    YulangClosure.PaperTypes.PaperCoreControl.StackTyped d old e stack a result →
      YulangClosure.PaperTypes.PaperCoreControl.StackTyped d new e stack a result
'YulangClosure.PaperTypes.PaperAllocationExecution.stack_graphWeaken' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.stack_graphWeaken

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.history_extension
@YulangClosure.PaperTypes.PaperAllocationExecution.history_extension : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {binder : YulangClosure.PaperTypes.TermName} {e : YulangClosure.PaperTypes.TypeEnvironment}
  {initialGraph : YulangClosure.PaperTypes.GraphEnvironment} {initialHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {initialState : YulangClosure.PaperTypes.PaperCoreControl.State} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {state : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest}
  (history :
    YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e initialGraph initialHeap initialState g heap
      state saved),
  YulangClosure.PaperTypes.GraphLookupPreserved initialGraph g ∧
    YulangClosure.PaperTypes.PaperAllocationExecution.HeapLookupPreserved initialHeap heap ∧
      ∃ front, heap = front ++ initialHeap
'YulangClosure.PaperTypes.PaperAllocationExecution.history_extension' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.history_extension

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperAllocationExecution.allocated_body_history
@YulangClosure.PaperTypes.PaperAllocationExecution.allocated_body_history : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {binder : YulangClosure.PaperTypes.TermName}
  {old : YulangClosure.PaperTypes.GraphEnvironment} {source e : YulangClosure.PaperTypes.TypeEnvironment}
  {rho : Nat → YulangClosure.PaperTypes.Value} {block : YulangClosure.PaperTypes.FreshHeap.Block}
  {heap : YulangClosure.PaperTypes.FreshHeap.Heap} {body : YulangClosure.PaperTypes.Computation}
  {stack : List YulangClosure.PaperTypes.Computation} {a result : YulangClosure.PaperTypes.Ty}
  {g : YulangClosure.PaperTypes.GraphEnvironment} {finalHeap : YulangClosure.PaperTypes.FreshHeap.Heap}
  {state : YulangClosure.PaperTypes.PaperCoreControl.State}
  {saved : List YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequest},
  YulangClosure.PaperTypes.PaperTemplateExecution.BodiesTyped d →
    (YulangClosure.PaperTypes.FreshHeap.ids block).Nodup →
      (∀ (r : Nat), r ∈ YulangClosure.PaperTypes.FreshHeap.ids block → ¬r ∈ List.map Prod.fst old) →
        (∀ (r : Nat), r ∈ YulangClosure.PaperTypes.FreshHeap.ids block → ¬r ∈ List.map Prod.fst heap) →
          YulangClosure.PaperTypes.TermSubstitutionTyped d old source e rho →
            YulangClosure.PaperTypes.FreshHeap.BlockTyped d old source block →
              YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d old e heap →
                YulangClosure.PaperTypes.PaperComputationTyped d old
                    (List.map Prod.snd (YulangClosure.PaperTypes.FreshHeap.formals block) ++ source) body a →
                  YulangClosure.PaperTypes.PaperCoreControl.StackTyped d old e stack a result →
                    ∀
                      (history :
                        YulangClosure.PaperTypes.PaperAllocationExecution.History d binder e
                          (YulangClosure.PaperTypes.FreshHeap.formals block ++ old)
                          (YulangClosure.PaperTypes.FreshHeap.allocate block rho heap)
                          {
                            head :=
                              YulangClosure.PaperTypes.replaceTermComputation
                                (YulangClosure.PaperTypes.graphFormalReplacements
                                  (YulangClosure.PaperTypes.FreshHeap.formals block) rho)
                                body,
                            stack := stack }
                          g finalHeap state saved),
                      YulangClosure.PaperTypes.GraphLookupPreserved old g ∧
                        YulangClosure.PaperTypes.PaperAllocationExecution.HeapLookupPreserved heap finalHeap ∧
                          YulangClosure.PaperTypes.FreshHeap.HeapPayloadTyped d g e finalHeap ∧
                            YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e state result ∧
                              YulangClosure.PaperTypes.PaperComputationTyped d g e
                                  (YulangClosure.PaperTypes.PaperCoreControl.erase state) result ∧
                                YulangClosure.PaperTypes.PaperAllocationExecution.SavedRequestsTyped d g e saved result
'YulangClosure.PaperTypes.PaperAllocationExecution.allocated_body_history' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperAllocationExecution.allocated_body_history
```

### Generated theorem inventory

All names have prefix `YulangClosure.PaperTypes.PaperAllocationExecution.`.

| Theorem | Complete transitive axiom list |
| --- | --- |
| `History.save.injEq` | `[propext, Quot.sound]` |
| `History.observedForce.inj` | `[propext, Quot.sound]` |
| `History.allocation.inj` | `[propext, Quot.sound]` |
| `exampleDeclaration.eq_1` | `[]` |
| `examplePacket.eq_1` | `[]` |
| `SavedRequest.mk.sizeOf_spec` | `[]` |
| `exampleTable.eq_1` | `[]` |
| `History.save.sizeOf_spec` | `[propext, Quot.sound]` |
| `exampleGraph.eq_1` | `[]` |
| `History.observedForce.sizeOf_spec` | `[propext, Quot.sound]` |
| `History.internal.injEq` | `[propext, Quot.sound]` |
| `exampleBlock.eq_1` | `[]` |
| `History.response.injEq` | `[propext, Quot.sound]` |
| `SavedRequest.mk.inj` | `[]` |
| `exampleHeap.eq_1` | `[propext, Quot.sound]` |
| `History.allocation.injEq` | `[propext, Quot.sound]` |
| `History.response.sizeOf_spec` | `[propext, Quot.sound]` |
| `History.observedForce.injEq` | `[propext, Quot.sound]` |
| `History.allocation.sizeOf_spec` | `[propext, Quot.sound]` |
| `History.internal.inj` | `[propext, Quot.sound]` |
| `History.brecOn.eq` | `[propext, Quot.sound]` |
| `History.response.inj` | `[propext, Quot.sound]` |
| `History.save.inj` | `[propext, Quot.sound]` |
| `History.initial.sizeOf_spec` | `[propext, Quot.sound]` |
| `SavedRequest.mk.injEq` | `[propext]` |
| `History.internal.sizeOf_spec` | `[propext, Quot.sound]` |
