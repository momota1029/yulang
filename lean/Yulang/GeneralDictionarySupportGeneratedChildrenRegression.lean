import Yulang.GeneralDictionarySupportGeneratedChildren
import Yulang.GeneralDictionarySupportRecursiveClassification
import Yulang.GeneralDictionarySupportRevisionObstruction

/-! Positive Joint-free recorded coverage and a reachable point-revision
boundary test. The latter asserts neither stable selection nor a V5 failure. -/
namespace Yulang.GeneralDictionarySupportGeneratedChildrenRegression
open GeneralNominalSaturationState GeneralDictionarySupportGeneratedChildren

namespace Positive
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalSupportExamples GeneralNominalExamples

theorem recorded : RecordedAt finish displayRoot 1 :=
  ⟨packet,List.mem_singleton_self _,rfl,rfl,GeneralDictionaryOrdinaryTrace.packet_extension packet⟩

theorem generated_without_joint : Generated finish.current displayRoot displayChild := by
  exact recorded_selected_generated registry registry_checked finish displayRoot displayRoot
    actual_reachable .root packet (List.mem_singleton_self _) rfl
    (GeneralDictionaryOrdinaryTrace.packet_extension packet) 1 [displayChild] rfl
    supported_parent_selected displayChild (List.mem_singleton_self _)
end Positive

namespace RevisionBoundary
open GeneralNominalFeedbackObstruction GeneralDictionaryCurrentRevisionObstruction
open GeneralDictionarySupportRevisionObstruction

theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence GeneralDeclarationExamples.roles)
    (generated : Generated finish.current root focus) : focus = root ∨ focus = child := by
  induction generated with
  | root => exact Or.inl rfl
  | @child parent focus prior edge ih =>
    have edges : finish.current.edges = [(root,child)] := by
      change [] ++ packet.children.map (fun c => (root,c)) = _
      rw [children_exact]; rfl
    rw [edges] at edge
    have same := List.mem_singleton.mp edge
    exact Or.inr (congrArg Prod.snd same)
  | @alias first last prior one two alias ih =>
    have sites : finish.current.sites = [GeneralNominalDemandMerging.pointSite root,
        GeneralNominalFeedbackSites.childSite packet child] := by
      change [GeneralNominalDemandMerging.pointSite root] ++ _ = _
      simp [GeneralNominalFeedbackSites.emitted,children_exact]
    rw [sites] at two
    rcases List.mem_cons.mp two with same | same
    · subst last; exact Or.inl rfl
    · have same := List.mem_singleton.mp same
      subst last; exact Or.inr rfl

/-- The emitted current child is not among the old generated occurrences.
This is a source-supported, modeled reachable snapshot, not a raw journal. -/
theorem new_child_not_generated : ¬ Generated finish.current root newChild := by
  intro generated
  rcases generated_cases newChild generated with same | same
  · have eq := congrArg (fun c => List.ofFn c.demand.arguments) same
    exact (by decide +kernel : ([(2,2)] : List GeneralSourceState.Interval) ≠ [(0,0)]) eq
  · have eq := congrArg (fun c => List.ofFn c.demand.arguments) same
    exact (by decide +kernel : ([(2,2)] : List GeneralSourceState.Interval) ≠ [(2,3)]) eq

/-- Historical child edges alone cannot cover every newly emitted current child
under unrestricted certified point reobservation. Stability is not asserted. -/
theorem reachable_emission_gap :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
      registry root finish ∧
    Models finish.current model ∧
    newChild ∈ GeneralNominalAllocation.children finish.current.context.state registry root
      declaration declaration_checked
      (GeneralNominalRecursiveInspection.bindings finish.current.context.state
        (GeneralNominalRecursiveCandidates.report finish.current.context declaration [((0 : Fin 4),(0 : Fin 4))])) ∧
    ¬ Generated finish.current root newChild := by
  refine ⟨reachable,GeneralDictionarySupportRevisionObstruction.modeled_nonempty.1,?_,new_child_not_generated⟩
  rw [revised_children]
  exact List.mem_singleton_self _
end RevisionBoundary
end Yulang.GeneralDictionarySupportGeneratedChildrenRegression
