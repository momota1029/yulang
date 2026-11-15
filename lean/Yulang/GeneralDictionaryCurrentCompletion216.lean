import Yulang.GeneralDictionaryCountedRawHead216
import Yulang.GeneralDictionaryMergeCriterion216
import Yulang.GeneralDictionaryDefault214ActualJournal

/-! Current corrected head/journal amalgamation, preserving an explicit finite
support. Agreement is retained by its actual origin roots. The overlap criterion
is exact for this support-preserving extension, not asserted for all traces. -/
namespace Yulang.GeneralDictionaryCurrentCompletion216
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralDictionaryCountedProjection216 (Agreement)
open GeneralDictionaryDefault214ActualJournal (journalSources)
open GeneralDictionaryMixedMerge216 (Overlap)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

def agreementSources (candidate : Plan roles) : List Nat :=
  (headInspection candidate).captures.filterMap fun entry => entry.origin.map originSource

theorem origin_member (member : entry ∈ (headInspection candidate).captures)
    (located : entry.origin = some origin) : originSource origin ∈ agreementSources candidate := by
  apply List.mem_filterMap.mpr
  exact ⟨entry,member,by rw [located]; rfl⟩

theorem agreement_iff (candidate : Plan roles) (first last : Assignment)
    (same : ∀ n ∈ agreementSources candidate, first n = last n) :
    Agreement candidate first ↔ Agreement candidate last := by
  constructor
  · intro valid a one b two names x y atX atY
    exact (GeneralNominalCenteredFrame179.same_iff x y
      (same _ (origin_member one atX)) (same _ (origin_member two atY))).mp
      (valid a one b two names x y atX atY)
  · intro valid a one b two names x y atX atY
    exact (GeneralNominalCenteredFrame179.same_iff x y
      (same _ (origin_member one atX)) (same _ (origin_member two atY))).mpr
      (valid a one b two names x y atX atY)

theorem completion_iff
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (pool : List Nat) (journal : journalSources state ⊆ pool)
    (origins : agreementSources candidate ⊆ pool)
    (endpoints : GeneralNominalAllocationSupport.Endpoints candidate.packet.bindings pool)
    (previous : Assignment) (valid : Models state previous) (agreement : Agreement candidate previous) :
    (∃ extended, Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended ∧
      (∀ n ∈ pool, extended n = previous n)) ↔
    Overlap candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
      candidate.packet.declaration candidate.packet.bindings pool previous := by
  constructor
  · rintro ⟨extended,_,head,kept⟩
    exact GeneralDictionaryMergeCriterion216.necessary _ _ _ _ _ pool endpoints previous extended kept
      (GeneralDictionaryCurrentBranch215.branch_merges candidate extended head)
  · intro overlap
    let extended := GeneralDictionaryMixedMerge216.patch candidate.packet.context.state candidate.packet.registry
      candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings pool previous
    have kept : ∀ n ∈ pool, extended n = previous n :=
      GeneralDictionaryMixedMerge216.preserves _ _ _ _ _ pool previous
    have journalValid : Models state extended :=
      (GeneralDictionaryDefault214ActualJournal.models_iff state (fun n h => (kept n (journal h)).symm)).mp valid
    have currentAgreement := (agreement_iff candidate previous extended (fun n h => (kept n (origins h)).symm)).mp agreement
    refine ⟨extended,journalValid,?_,kept⟩
    exact (GeneralDictionaryCountedRawHead216.head_iff_merges source point ground coverage path candidate frame
      extended journalValid currentAgreement).mpr (GeneralDictionaryMixedMerge216.merges_valid overlap endpoints)


noncomputable def support (state : State roles) (candidate : Plan roles) : List Nat :=
  journalSources state ++ agreementSources candidate ++
    candidate.packet.bindings.flatMap (fun binding => [binding.2.1,binding.2.2])

theorem support_endpoints (state : State roles) (candidate : Plan roles) :
    GeneralNominalAllocationSupport.Endpoints candidate.packet.bindings (support state candidate) := by
  intro binding member
  constructor
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨binding,member,by simp⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨binding,member,by simp⟩)

/-- Eliminate unconstrained aggregate assignments from common head feasibility.
The remaining existential still includes actual capture agreement and overlap;
this is not a proof of their automatic satisfaction at every selected state. -/
theorem common_iff
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate) :
    (∃ model, Models state model ∧ Agreement candidate model ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model) ↔
    ∃ model, Models state model ∧ Agreement candidate model ∧
      Overlap candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
        candidate.packet.declaration candidate.packet.bindings (support state candidate) model := by
  constructor
  · rintro ⟨model,valid,agreement,head⟩
    refine ⟨model,valid,agreement,?_⟩
    exact GeneralDictionaryMergeCriterion216.necessary _ _ _ _ _ _ (support_endpoints state candidate)
      model model (fun _ _ => rfl) (GeneralDictionaryCurrentBranch215.branch_merges candidate model head)
  · rintro ⟨model,valid,agreement,overlap⟩
    have journal : journalSources state ⊆ support state candidate :=
      fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
    have origins : agreementSources candidate ⊆ support state candidate :=
      fun _ h => List.mem_append_left _ (List.mem_append_right _ h)
    obtain ⟨extended,newValid,head,kept⟩ :=
      (completion_iff source point ground coverage path candidate frame (support state candidate)
        journal origins (support_endpoints state candidate) model valid agreement).mpr overlap
    exact ⟨extended,newValid,(agreement_iff candidate model extended
      (fun n h => (kept n (origins h)).symm)).mp agreement,head⟩

end Yulang.GeneralDictionaryCurrentCompletion216
