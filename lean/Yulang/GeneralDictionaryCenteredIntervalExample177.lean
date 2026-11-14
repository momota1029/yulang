import Yulang.GeneralDictionaryCenteredScalarIntervals177
import Yulang.GeneralDictionaryCenteredRootExample177
import Yulang.GeneralNominalNonpointInspectionExamples

/-! A modeled, empty-journal centered state with a genuine int/top interval.
This example does not assert reachability from the ground point-root boundary. -/
namespace Yulang.GeneralDictionaryCenteredIntervalExample177
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryScalarIntervalInspection

abbrev state : GeneralNominalState.State where
  seed := 1
  base := GeneralNominalExamples.base true
  view := GeneralNominalExamples.view true
  constructors := GeneralDictionaryFiniteObservedExample.constructors
  nominals := fun _ => none
  catalogue := by intro _ _ impossible; cases impossible
  bodies_opaque := by intro _ _ impossible; cases impossible
abbrev context : Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev declaration := GeneralNominalExamples.intDisplay
abbrev registry := GeneralDictionaryCenteredRootExample177.registry
abbrev root : Occurrence roles := ⟨178,⟨0,fun _ => (1,0),[],by simp⟩⟩
abbrev start := initial context root
abbrev model : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source = 0 then .top else .base .int,Common.rowEmpty)

theorem source_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
  · intro atom member
    change atom ∈ GeneralSourceState.equationAtoms (1 : Fin 2) (.base .int) at member
    simp only [GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot term recorded
    by_cases yes : slot = 1
    · subst slot
      have equal : (.base .int : Core.PresenceGeneration.TyTerm (Fin 2)) = term := by
        simpa [GeneralNominalExamples.heads,GeneralSourceState.Head.equation] using recorded
      subst term
      exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
    · simp [GeneralNominalExamples.heads,yes,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [GeneralNominalExamples.base,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro slot descriptor impossible; cases impossible

theorem endpoint_order : CommonNominalFullCarrier.Subtype (model 1).1 (model 0).1 :=
  GeneralNominalNonpointInspectionExamples.int_top

theorem inhabited : Models start model := by
  apply (initial_models context root model).mpr
  refine ⟨source_models,?_⟩
  intro index
  constructor
  · change CommonNominalFullCarrier.Subtype (.base .int) _
    by_cases zero : (rootSite state.seed root).center index = 0
    · simp only [zero]; exact GeneralNominalNonpointInspectionExamples.int_top
    · simp only [zero]; exact CommonNominalFullCarrier.subtype_refl _
  · change CommonNominalFullCarrier.Subtype (if (rootSite state.seed root).center index = 0 then .top else .base .int) .top
    split
    · exact CommonNominalFullCarrier.subtype_refl _
    · exact GeneralNominalNonpointInspectionExamples.int_top

abbrev shape : Shape context root declaration where
  role := rfl
  entries := [((1,0),.int)]
  observed := by intro entry member; cases List.mem_singleton.mp member; exact ⟨rfl,rfl⟩
  inputs := rfl
  query := by simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,queries]
  located := by decide +kernel
  defined := by intro output member; cases member

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,
    GeneralDictionaryCenteredRootExample177.checked,[(1,0)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite state.seed root,rfl⟩

theorem branch : packet.Holds model := by
  have priv := private_models registry context root declaration shape model source_models (by
    intro pair member
    cases List.mem_singleton.mp member
    exact endpoint_order)
  refine ⟨priv.1,priv.2,?_⟩
  rw [GeneralDictionaryLinearLeaf.generated_empty _ _ _ _ _ rfl rfl]
  exact GeneralNominalMaterialization.empty_models ..

theorem prepared : Prepared registry context root declaration packet.checked := by
  refine ⟨?_,?_,?_,[(1,0)],shape.located,?_,?_,model,branch⟩
  · exact GeneralDictionaryFiniteObservedExample.metadata
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · intro key _ present
    have below : GeneralNominalAllocation.source state registry root.identity key ≤ state.seed := by
      simp [GeneralNominalState.sources,List.ofFn_succ] at present
      rcases present with h | h | h | h <;> rw [h] <;> decide +kernel
    exact False.elim (GeneralNominalAllocation.source_initial_fresh state registry root.identity key _ below rfl)
  · change Finished (report context declaration (intervals shape.entries))
    rw [report_exact context root declaration shape]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · exact shape.defined
    · rw [GeneralDictionaryLinearLeaf.generated_empty _ _ _ _ _ rfl rfl]

theorem candidate : GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,by simp [start,initial,initialAt,GeneralNominalSupport.initial,
    GeneralNominalSaturationState.initial,rootSite],by simp [start,initial,initialAt],by simp,rfl,
    shape.located,prepared,model,branch⟩
  exact GeneralDictionaryLinearLeaf.children_empty context registry root declaration packet.checked rfl _

theorem evidence : GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) :=
  GeneralDictionaryCenteredScalarIntervals177.candidate_evidence candidate [.int] rfl rfl rfl shape.query model inhabited

theorem nonpoint : (root.demand.arguments ⟨0,by decide⟩).1 ≠ (root.demand.arguments ⟨0,by decide⟩).2 := by decide +kernel

theorem regression : Models start model ∧ start.plans = [] ∧ start.erased.current.packets = [] ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) ∧
    (root.demand.arguments ⟨0,by decide⟩).1 ≠ (root.demand.arguments ⟨0,by decide⟩).2 :=
  ⟨inhabited,rfl,rfl,evidence,nonpoint⟩

end Yulang.GeneralDictionaryCenteredIntervalExample177
