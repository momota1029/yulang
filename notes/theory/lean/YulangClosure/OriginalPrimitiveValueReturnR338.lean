import YulangClosure.OriginalSourceScopedInterpretationR335
import YulangClosure.OriginalCalleeArgumentHistoryR312

/-!
R338: the operation VALUE Return before argument preparation or Request.

This is a constructor-data projection of machine.rs Operation/data/allocate
and receiving.rs opaque into the EXISTING R312 Raw/Metadata/Control types.
`ValueKind.retained` is that representation's opaque non-computation tag: it
does not identify an operation declaration with a semantic Provider or retain
the full native SourceOperationResolution. No new original Inputs, primitive
license, traceForm interpretation or kernel.atom meaning is defined here.

The positive application is to R312.returnTop: this allocation returns the
callee, and the next argument allocation has a distinct value handle. The
negative application is to the original Return trace consumer: allocation
changes the represented world already, so its post-allocation result cannot
be checked at the pre-allocation Event. Neither application constructs R159's
independent primitive atom or R306's licensed source contribution.
-/
namespace YulangClosure.OriginalPrimitiveValueReturnR338

open OriginalSource NativeClosureEnvironment SourceIdentityWorld OriginalWorldReadout
open OriginalCalleeDelayProvenance OriginalCalleeArgumentHistoryR312
open OriginalSourceInterpretation OriginalParameterSemantics
open OriginalSourceScopedInterpretationR335

variable {C Dict Rest Schema : Type}
local notation "R" => OriginalCalleeDelayProvenance.Raw C Dict Rest Schema

/-- `allocate(site, Operation(resolution), None)` in the existing opaque-kind
projection. The sparse executable map is untouched, including malformed raw
maps; fresh-index absence is not fabricated from the allocation operation. -/
def allocateValue (raw : R) (site tag : Nat) : R :=
  {raw with values := raw.values ++ [⟨site, .retained tag⟩]}

/-- The exact opaque metadata written by receiving.rs; no receipt is added. -/
def opaqueMetadata : Metadata := ⟨none, true, .ordinary⟩

def data (raw : R) (site tag : Nat) : R :=
  appendView (allocateValue raw site tag) raw.values.length opaqueMetadata

def returned (raw : R) : Received Nat :=
  ⟨raw.values.length, .value, raw.views.length, none⟩

def returnedMachine (raw : R) (site tag : Nat) (frames : List Frame) :
    OriginalCalleeArgumentHistoryR312.Machine (data raw site tag) :=
  ⟨.returned (returned raw), frames⟩

/-- All raw constructor fields are computed, not assumed post-state equations. -/
theorem data_fields (raw : R) (site tag : Nat) :
    (data raw site tag).values = raw.values ++ [⟨site, .retained tag⟩] ∧
    (data raw site tag).views = raw.views ++ [⟨raw.values.length, opaqueMetadata⟩] ∧
    (data raw site tag).executables = raw.executables ∧
    (data raw site tag).program = raw.program ∧
    (data raw site tag).skeleton = raw.skeleton := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The returned value and its exact opaque view are allocated at the old
vector lengths. No actual semantic provider relation follows from this fact. -/
theorem returned_cells (raw : R) (site tag : Nat) :
    (vectorStore ((data raw site tag).values.map some)).cell (returned raw).value =
      some ⟨site, .retained tag⟩ ∧
    (project (data raw site tag)).world.receiving.views.cell (returned raw).view =
      some ⟨(returned raw).value, opaqueMetadata⟩ := by
  constructor
  · simp only [data, appendView, allocateValue, returned, List.map_append,
      List.map_cons, List.map_nil, vector_store_push]
    simpa only [vectorStore, List.length_map] using
      push_current (vectorStore (raw.values.map some))
        (⟨site, .retained tag⟩ : RuntimeValue)
  · simp only [data, appendView, project, allocateValue, returned,
      List.map_append, List.map_cons, List.map_nil, vector_store_push]
    simpa only [vectorStore, List.length_map] using
      push_current (vectorStore (raw.views.map some))
        (⟨raw.values.length, opaqueMetadata⟩ : SourceIdentityWorld.View Nat Metadata)

theorem returned_matches (raw : R) (site tag : Nat) :
    Matches (project (data raw site tag)).world.receiving (returned raw) :=
  ⟨_, (returned_cells raw site tag).2, rfl⟩

/-- Allocation writes no invocation, lexical cell, receipt, receipt index or
dictionary state; only the projected receiving view store grows. -/
theorem data_world_fields (raw : R) (site tag : Nat) :
    (project (data raw site tag)).world.control = (project raw).world.control ∧
    (project (data raw site tag)).world.environments = (project raw).world.environments ∧
    (project (data raw site tag)).world.cells = (project raw).world.cells ∧
    (project (data raw site tag)).world.receiving.receipts =
      (project raw).world.receiving.receipts ∧
    (project (data raw site tag)).world.receiving.index =
      (project raw).world.receiving.index ∧
    (project (data raw site tag)).world.rest = (project raw).world.rest ∧
    (project (data raw site tag)).world.receiving.views.size =
      (project raw).world.receiving.views.size + 1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [project, data, appendView, allocateValue, vectorStore]

/-- A genuine allocation cannot use the old native Configuration verbatim. -/
theorem data_changes_world (raw : R) (site tag : Nat) :
    (project (data raw site tag)).world ≠ (project raw).world := by
  intro same
  have growth := (data_world_fields raw site tag).2.2.2.2.2.2
  rw [same] at growth
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) growth

/-- Applied to the EXISTING CalRet consumer with its actual saved frame.
The pending argument is prepared only after this returned-control pair. -/
theorem operation_return_enters_calRet (raw : R) (site tag : Nat)
    (saved : SavedCallee) (tail : List Frame) :
    returnTop (data raw site tag)
      (returnedMachine raw site tag (.callee saved :: tail)) =
      some (saved, returned raw, tail,
        prepare (data raw site tag) saved.call.site saved.argumentLabel saved.callerEnvironment) := rfl

/-- R312's subsequent Delay allocation uses the next value index, not the
callee's already allocated handle, regardless of its saved argument code. -/
theorem argument_handle_distinct (raw : R) (site tag : Nat) :
    (data raw site tag).values.length = (returned raw).value + 1 ∧
    (data raw site tag).values.length ≠ (returned raw).value := by
  have size : (data raw site tag).values.length = (returned raw).value + 1 := by
    simp [data, appendView, allocateValue, returned]
  refine ⟨size, ?_⟩
  rw [size]
  exact Nat.succ_ne_self _

/-- The actual tick declaration source row determines this projection's tag;
its complete physical declaration remains R321.tick, not this numeric tag. -/
def tickData (origin : Declaration) (raw : R) : R :=
  data raw (tickPrimitive origin).site (tickPrimitive origin).identifier

theorem tick_declared_value_return (origin : Declaration) (raw : R) :
    OriginalSourceScopedInterpretationR335.readPrimitive origin []
      OriginalModuleContextBindingR315.makeInitializer
      (tickRequest origin).operands.callee.key .primitiveDeclarationInstance =
        some (tickPrimitive origin) ∧
    (vectorStore ((tickData origin raw).values.map some)).cell (returned raw).value =
      some ⟨(tickPrimitive origin).site, .retained (tickPrimitive origin).identifier⟩ ∧
    Matches (project (tickData origin raw)).world.receiving (returned raw) :=
  ⟨tick_scoped_declaration_resolves origin, (returned_cells raw _ _).1,
    returned_matches raw _ _⟩

/-- All original Event fields remain arbitrary; only actual native world
readout equations are needed to distinguish the two allocation phases. -/
theorem allocation_events_differ
    {b : Sorts} {Body View : Type}
    (raw : R) (site tag : Nat)
    (before after : Event (NS b (OriginalValueEntryDemand.Dispatch C) Nat Metadata Site Rest Body View))
    (pre : before.current.world = (project raw).world)
    (post : after.current.world = (project (data raw site tag)).world) :
    after ≠ before := by
  intro same
  apply data_changes_world raw site tag
  exact post.symm.trans ((congrArg (fun event => event.current.world) same).trans pre)

/-- Actual original Return consumer applied to this native constructor.
The post-allocation value cannot appear as a pre-allocation trace result.
Inputs stays independently fixed; no traceForm or provider law is invented. -/
theorem pre_allocation_trace_rejected
    {b : Sorts} {Body View : Type}
    (inputs : Inputs (NS b (OriginalValueEntryDemand.Dispatch C) Nat Metadata Site Rest Body View))
    (raw : R) (site tag : Nat)
    (before : Event (NS b (OriginalValueEntryDemand.Dispatch C) Nat Metadata Site Rest Body View))
    (result : ValueRow (NS b (OriginalValueEntryDemand.Dispatch C) Nat Metadata Site Rest Body View))
    (pre : before.current.world = (project raw).world)
    (post : result.event.current.world = (project (data raw site tag)).world)
    (observation : b.Observation) (interface : b.Interface)
    (form : inputs.traceForm ⟨interface, observation, before⟩ = .pureReturn result) :
    ¬ Meaning inputs (.trace ⟨interface, observation, before⟩) := by
  intro valid
  have same := ((return_observation_iff inputs _ result form).mp valid).2.2.2.1.1
  exact allocation_events_differ raw site tag before result.event pre post same

end YulangClosure.OriginalPrimitiveValueReturnR338
