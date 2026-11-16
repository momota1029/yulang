import Yulang.GeneralDictionaryHeadSharingSpecification220

/-! Finite amalgamation for separated aggregate slots or singleton captures.
No separation claim is made for arbitrary historical allocations. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryHeadSharingAmalgamation220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208 (Step)
open GeneralDictionaryMergeCompletion216 (Separate)
open GeneralDictionaryMixedMerge216 (Overlap)
open GeneralDictionaryMergeSlots216 (active)
open GeneralNominalAllocation (occurrences)
variable {roles : Roles.RoleDecls} {state : State roles}
variable {registry : Registry} {root focus : Occurrence roles}

theorem overlap_of_separate
    (separate : Separate snapshot registry invocation declaration bindings pool)
    (model : GeneralNominalCommonBridge.Assignment) :
    Overlap snapshot registry invocation declaration bindings pool model := by
  exact ⟨fun i member => False.elim ((separate i).1 member),
    fun i member => False.elim ((separate i).2 member)⟩

theorem active_empty_of_singletons
    (singletons : ∀ name ∈ declaration.inputNames, ∃ pair, occurrences bindings name = [pair]) :
    active declaration bindings = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  obtain ⟨declared,selected⟩ := List.mem_filter.mp member
  obtain ⟨pair,equal⟩ := singletons name declared
  simp [equal] at selected

theorem separate_of_singletons
    (singletons : ∀ name ∈ declaration.inputNames, ∃ pair, occurrences bindings name = [pair]) :
    Separate snapshot registry invocation declaration bindings pool := by
  intro i
  have empty := active_empty_of_singletons singletons
  have impossible := i.isLt
  have no : (active declaration bindings).length = 0 := congrArg List.length empty
  omega

variable (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)

include checked source point ground coverage path frame
theorem common_iff_of_separate
    (separate : Separate candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings
      (GeneralDictionaryCurrentCompletion216.support state candidate)) :
    (∃ model, Models state model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate model) ↔
    ∃ model, Models state model ∧ GeneralDictionaryHeadSharing220.Holds candidate model := by
  rw [GeneralDictionaryHeadSharingSpecification220.common_iff_sharing_overlap
    checked source point ground coverage path candidate frame]
  constructor
  · rintro ⟨model,valid,sharing,_⟩
    exact ⟨model,valid,sharing⟩
  · rintro ⟨model,valid,sharing⟩
    exact ⟨model,valid,sharing,overlap_of_separate separate model⟩

theorem common_iff_of_singletons
    (singletons : ∀ name ∈ candidate.packet.declaration.inputNames,
      ∃ pair, occurrences candidate.packet.bindings name = [pair]) :
    (∃ model, Models state model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate model) ↔
    ∃ model, Models state model ∧ GeneralDictionaryHeadSharing220.Holds candidate model :=
  common_iff_of_separate checked source point ground coverage path candidate frame
    (separate_of_singletons singletons)

omit frame in
/-- Feasible chooses the frame; separation is required on each eligible frame. -/
theorem feasible_common_of_separate
    (feasible : GeneralDictionaryHeadSharingConflict220.Feasible registry state focus key)
    (separate : ∀ candidate : Plan roles,
      GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate →
      Separate candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings
        (GeneralDictionaryCurrentCompletion216.support state candidate)) :
    ∃ candidate : Plan roles,
      GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate ∧
      ∃ model, Models state model ∧
        GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
          candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ∧
        GeneralNominalCenteredHeadOutputs.HeadEquations candidate model := by
  obtain ⟨model,valid,candidate,framed,sharing⟩ := feasible
  exact ⟨candidate,framed,(common_iff_of_separate checked source point ground coverage path
    candidate framed (separate candidate framed)).mpr ⟨model,valid,sharing⟩⟩

end Yulang.GeneralDictionaryHeadSharingAmalgamation220
