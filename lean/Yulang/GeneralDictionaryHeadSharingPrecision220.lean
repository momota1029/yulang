import Yulang.GeneralDictionaryHeadSharing220

/-! Self equations carry no extra restriction on actual origins of a finished
candidate. Functionality is derived from canonical structural projections and
nominal invariance, rather than assumed for arbitrary constructors. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryHeadSharingPrecision220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalInspectionAlignment
open GeneralNominalOriginTerms
open GeneralNominalReadbackFunctionality (Unique source_unique projection_unique)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

mutual
 theorem schema_unique (state : GeneralNominalState.State) (model : Assignment)
    (query : Query) (bounds : Bounds state) (origin : Origin)
    (unique : Unique model origin)
    (finished : Finished (inspect state query bounds (some origin)))
    (entry : Use) (member : entry ∈ (schema query origin .actual).variables) :
    Unique model entry.origin := by
  cases query with
  | variables names =>
    simp only [schema] at member
    obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
    exact unique
  | scalar base => simp [schema] at member
  | deferred reason => simp [schema] at member
  | node shape children =>
    simp only [schema] at member
    simp only [inspect,finished_visit] at finished
    split at finished
    · rename_i lowerKind lows upperKind ups lowerAt upperAt
      split at finished
      · rename_i matching
        have canonical : shape.Canonical := matching.1 ▸ state.view.canonical lowerKind
        have slotsLength : ((List.ofFn lows).zip (List.ofFn ups)).length = shape.arity := by
          simp only [List.length_zip,List.length_ofFn,matching.1,matching.2,Nat.min_self]
        exact schemas_unique state model children _ (fun i => .structural origin shape i) 0
          (fun index => by
            have within : index.val < shape.arity := by rw [← slotsLength]; exact index.isLt
            simpa only [project,Nat.zero_add] using projection_unique unique (.structural shape) canonical ⟨index.val,within⟩)
          finished entry member
      · simp only [Finished,block] at finished; cases finished.1
    · simp only [Finished] at finished; cases finished.2.1
    · simp only [Finished,block] at finished; cases finished.1
  | nominal name children =>
    simp only [schema] at member
    obtain ⟨descriptor,intervals,_,_,_,complete,_⟩ :=
      nominal_left state children bounds (some origin) finished
    have length := finished_length state children intervals _ 0 complete
    exact schemas_unique state model children intervals (fun i => .nominal origin name i) 0
      (fun index => by
        have within : index.val < children.length := by rw [length]; exact index.isLt
        simpa only [project,Nat.zero_add] using projection_unique unique (.nominal name children.length) trivial ⟨index.val,within⟩)
      complete entry member
 termination_by sizeOf query

 theorem schemas_unique (state : GeneralNominalState.State) (model : Assignment)
    (queries : List Query) (bounds : List (Bounds state)) (origins : Nat → Origin) (offset : Nat)
    (unique : ∀ index : Fin bounds.length, Unique model (origins (offset + index.val)))
    (finished : Finished (inspectMany state queries bounds (fun i => some (origins i)) offset))
    (entry : Use) (member : entry ∈ (schemas queries origins .actual offset).variables) :
    Unique model entry.origin := by
  cases queries with
  | nil => simp [schemas] at member
  | cons query rest => cases bounds with
    | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons first tail =>
      simp only [inspectMany,finished_append] at finished
      simp only [schemas,Schema.append,List.mem_append] at member
      rcases member with present | present
      · exact schema_unique state model query first (origins offset)
          (by simpa only [Nat.add_zero] using unique ⟨0,by simp⟩) finished.1 entry present
      · exact schemas_unique state model rest tail origins (offset+1)
          (fun index => by simpa only [Nat.add_assoc,Nat.add_comm 1] using unique ⟨index.val+1,by simp⟩)
          finished.2 entry present
 termination_by sizeOf queries
end

theorem head_unique (candidate : Plan roles) (model : Assignment)
    (finished : Finished (headInspection candidate)) (entry : Use)
    (member : entry ∈ candidate.headSchema.variables) : Unique model entry.origin :=
  schemas_unique candidate.packet.context.state model _ candidate.packet.bounds
    (fun index => .source ((List.ofFn candidate.input.center)[index]?.getD 0)) 0
    (fun _ => source_unique model _) finished entry member

theorem head_seen
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (entry : Use)
    (member : entry ∈ candidate.headSchema.variables) : ∃ value, Observes model entry.origin value := by
  have tests := GeneralDictionaryCountedCandidate216.tests source point ground coverage path candidate frame model valid
  have bounds := GeneralDictionaryRecursiveBounds215.many_bounds candidate.packet.context.state model
    (frame.context_eq.symm ▸ valid.1) _ candidate.packet.bounds _ 0
    (fun index => by simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds candidate frame model valid index)
    tests
  obtain ⟨captured,present,_,origin⟩ := GeneralNominalSchemaCapture187.schemas_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0
    (GeneralDictionaryDefaultRevisit214.frame_finished frame) entry member
  exact (bounds _ (GeneralNominalCaptureAnchors.many_anchored candidate.packet.context.state _
    candidate.packet.bounds _ 0 captured present entry.origin origin)).1

theorem head_self
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (entry : Use)
    (member : entry ∈ candidate.headSchema.variables) : Same model entry.origin entry.origin :=
  ⟨head_seen source point ground coverage path candidate frame model valid entry member,
    head_seen source point ground coverage path candidate frame model valid entry member,
    head_unique candidate model (GeneralDictionaryDefaultRevisit214.frame_finished frame) entry member⟩

def NoDistinctSameName (candidate : Plan roles) : Prop :=
  ∀ first ∈ candidate.headSchema.variables, ∀ last ∈ candidate.headSchema.variables,
    first.name = last.name → first.origin = last.origin

theorem no_distinct_same_name_of_nodup (candidate : Plan roles)
    (distinct : (candidate.headSchema.variables.map Use.name).Nodup) : NoDistinctSameName candidate := by
  intro first one last two names
  obtain ⟨i,hi,atI⟩ := List.mem_iff_getElem.mp one
  obtain ⟨j,hj,atJ⟩ := List.mem_iff_getElem.mp two
  have hi' : i < (candidate.headSchema.variables.map Use.name).length := by simpa using hi
  have hj' : j < (candidate.headSchema.variables.map Use.name).length := by simpa using hj
  have equal : i = j := distinct.eq_of_getElem_eq hi' hj' (by
    simpa only [List.getElem_map,atI,atJ] using names)
  cases equal
  exact congrArg Use.origin (atI.symm.trans atJ)

theorem holds_of_no_distinct_same_name
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (distinct : NoDistinctSameName candidate) :
    GeneralDictionaryHeadSharing220.Holds candidate model := by
  apply (GeneralDictionaryHeadSharing220.holds_iff candidate model).mpr
  intro first one last two names
  rw [← distinct first one last two names]
  exact head_self source point ground coverage path candidate frame model valid first one

end Yulang.GeneralDictionaryHeadSharingPrecision220
