import Yulang.GeneralDictionarySupportBindingGeneration
import Yulang.GeneralDictionarySupportGeneratedChildrenRegression

/-! Binding transport regressions. The recorded positive case needs no Joint.
The actual point revision is correctly rejected by the binding certificate;
its model equivalence is not mistaken for source-ID capture equality. -/
namespace Yulang.GeneralDictionarySupportBindingGenerationRegression
open GeneralDictionarySupportBindingGeneration GeneralNominalSaturationState

namespace Positive
open GeneralDictionarySupportRecursiveExample GeneralDictionarySupportRecursiveClassification
open GeneralNominalSupportExamples GeneralNominalExamples

theorem bindings : BindingsAt packet finish.current.context :=
  bindings_of_extension packet finish.current.context rfl
    (GeneralDictionaryOrdinaryTrace.packet_extension packet)

theorem generated_without_extension_premise : Generated finish.current displayRoot displayChild :=
  recorded_selected_generated registry registry_checked finish displayRoot displayRoot
    actual_reachable .root packet (List.mem_singleton_self _) rfl bindings
    1 [displayChild] rfl supported_parent_selected displayChild (List.mem_singleton_self _)
end Positive

namespace RevisionBoundary
open GeneralNominalFeedbackObstruction GeneralDictionaryCurrentRevisionObstruction
open GeneralDictionarySupportRevisionObstruction

theorem seed_preserved : finish.current.context.state.seed = packet.context.state.seed :=
  packet_seed registry root finish
    (GeneralNominalSupportBoundary.reachable_formed registry finish root reachable)
    packet (List.mem_singleton_self _)

/-- Equal model sets and equal allocation seeds do not force capture equality. -/
theorem changed_bindings : ¬ BindingsAt packet finish.current.context := by
  rintro ⟨bounds,found,same⟩
  have located : GeneralNominalRecursiveCandidates.arguments finish.current.context packet.site.occurrence =
      some [((0 : Fin 4),(0 : Fin 4))] := rfl
  have equal := Option.some.inj (found.symm.trans located)
  subst bounds
  change GeneralNominalRecursiveInspection.bindings revised.context.state
    (GeneralNominalRecursiveCandidates.report revised.context declaration [((0 : Fin 4),(0 : Fin 4))]) = packet.bindings at same
  rw [revised_report] at same
  unfold Packet.bindings at same
  rw [GeneralNominalFeedbackObstruction.report_exact] at same
  have different : ([(0,(2,2))] : GeneralNominalAllocation.Bindings) ≠ [(0,(2,3))] := by decide +kernel
  exact different same
end RevisionBoundary
end Yulang.GeneralDictionarySupportBindingGenerationRegression
