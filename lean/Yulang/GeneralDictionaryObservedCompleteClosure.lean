import Yulang.GeneralDictionaryObservedCompleteFinalEvidence
import Yulang.GeneralDictionarySupportRecursiveClosure

namespace Yulang.GeneralDictionaryObservedCompleteClosure
open GeneralDictionaryObservedCompleteExample GeneralDictionaryObservedCompleteInstallation
open GeneralDictionaryObservedCompleteEvidence GeneralDictionaryObservedCompleteFinalEvidence
open GeneralNominalExamples (model listDescriptor intDisplay)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

noncomputable abbrev current := installed.current.context

theorem final_parent_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Instance registry current assignment root declaration.id children :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry context current
    (GeneralDictionaryOrdinaryTrace.packet_extension packet) assignment valid.1 root declaration.id children
    (GeneralDictionaryObservedTreeBranch.instance_of_shape context registry root declaration
      (by simp) checked shape metadata assignment (source_of_models assignment valid))

theorem final_child_instance (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : Models installed.current assignment) :
    Instance registry current assignment child intDisplay.id [] :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry context current
    (GeneralDictionaryOrdinaryTrace.packet_extension packet) assignment valid.1 child intDisplay.id []
    (child_instance assignment (source_of_models assignment valid))

theorem edges_exact : installed.current.edges = [(root,child)] := by
  change [] ++ packet.children.map (fun c => (root,c)) = _
  rw [packet_children,children_exact]; rfl

theorem sites_exact : installed.current.sites =
    [GeneralNominalDemandMerging.pointSite root,GeneralNominalFeedbackSites.childSite packet child] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ packet.children.map (GeneralNominalFeedbackSites.childSite packet) = _
  rw [packet_children,children_exact]; rfl

theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated installed.current root focus) : focus = root ∨ focus = child := by
  induction generated with
  | root => exact Or.inl rfl
  | child _ member _ =>
    rw [edges_exact] at member
    have same := List.mem_singleton.mp member
    exact Or.inr (congrArg Prod.snd same)
  | alias _ _ member _ _ =>
    rw [sites_exact] at member
    rcases List.mem_cons.mp member with same | rest
    · subst same; exact Or.inl rfl
    · have same := List.mem_singleton.mp rest
      subst same; exact Or.inr rfl

theorem merges_closed (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ installed.current.sites) (two : last ∈ installed.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs installed.current first last) :
    Alias installed.current first.occurrence.identity last.occurrence.identity := by
  rw [sites_exact] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  · exact .refl _
  · have wrong := same.1; cases wrong
  · have wrong := same.1; cases wrong
  · exact .refl _

abbrev varying := GeneralDictionaryTerminalRefresh.varying

theorem varying_model (name : Nat) (large : 2 ≤ name) : Models installed.current (varying name) :=
  models_of_source _ (GeneralDictionarySupportRecursiveClosure.varying_source name large)

theorem refresh_large_unknown (next : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCycleSteps.Refresh installed.current next) (id : Nat) (large : 2 ≤ id) :
    ¬ GeneralNominalState.Known next.state id :=
  GeneralDictionaryTerminalRefresh.no_known_distinct next.state model (varying id) id
    (by change (if id = 0 then CommonNominalFullCarrier.nominal 0 [.inl (.base .int)] else .base .int) = .base .int; exact ite_eq_right (by omega))
    (by simp only [varying,GeneralDictionaryTerminalRefresh.varying,ite_true]; rfl)
    (certificate.exact _ (models_of_source model source_models)) (certificate.exact _ (varying_model id large))

theorem context_complete : ContextComplete installed.current := by
  intro m valid
  have growth := GeneralDictionaryOrdinaryTrace.packet_extension packet
  obtain ⟨reserved,atoms,allocated,equal⟩ := growth
  change current = GeneralDictionaryOrdinaryTrace.extendContext context reserved atoms allocated at equal
  change GeneralNominalState.Models current.state m at valid
  rw [equal] at valid
  exact models_of_source m ((GeneralDictionaryOrdinaryTransport.models_extended allocated reserved atoms context.state m).mp valid).1

theorem point_closed : GeneralNominalReobservationSteps.PointClosed current.state := by
  intro slot descriptor recorded
  change Fin 2 at slot
  change (if slot = (0 : Fin 2) then some listDescriptor else none) = some descriptor at recorded
  by_cases zero : slot = (0 : Fin 2)
  · subst slot
    have same := Option.some.inj recorded
    subst descriptor
    intro parameter member
    have same := List.mem_singleton.mp member
    subst parameter
    exact rfl
  · simp [zero] at recorded
end Yulang.GeneralDictionaryObservedCompleteClosure
