import Yulang.GeneralDictionarySettledRecursiveExample

/-! The actual recursive fixture cannot take the terminal-child install needed
by the consumer-resumption contract. Ordinary novelty already fails. -/
namespace Yulang.GeneralDictionaryRecursiveConsumerObstruction
open GeneralDictionarySupportRecursiveExample
open GeneralDictionarySupportRecursiveClassification
open GeneralDictionarySupportRecursiveClosure
open GeneralNominalExamples GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)

/-- Generatedness is witnessed by the actual recorded parent-child edge. -/
theorem child_generated : Generated finish.current displayRoot displayChild := by
  apply Generated.child Generated.root
  rw [edges_exact]
  exact List.mem_singleton_self _

/-- No terminal-child novelty can be supplied, even before checking I26 guards.
No installability existence is claimed by this conditional result. -/
theorem child_installable_committed (leaf : Packet roles)
    (site : leaf.site.occurrence = displayChild)
    (enabled : GeneralNominalFeedbackSteps.Installable registry finish.current leaf) :
    GeneralNominalFeedbackSteps.Committed finish.current leaf :=
  installs_committed leaf (by rw [site]; exact child_generated) enabled

/-- In particular, the installation premises of the resumption contract have
no witness at this concrete final state. The explicit new guard is retained. -/
theorem no_child_install_contract : ¬ ∃ leaf : Packet roles, ∃ support,
    leaf.site.occurrence = displayChild ∧ leaf.children = [] ∧
    GeneralNominalFeedbackSteps.Installable registry finish.current leaf ∧
    ¬ GeneralNominalFeedbackSteps.Committed finish.current leaf ∧
    GeneralNominalSettledSteps.PacketGuard finish leaf support := by
  rintro ⟨leaf,support,site,_,enabled,novel,_⟩
  exact novel (child_installable_committed leaf site enabled)

/-- Actual guarded stability excludes all child operations, not merely install. -/
theorem no_child_at (after : GeneralNominalSupport.Tracked roles) :
    ¬ GeneralNominalSettledSteps.At registry finish displayChild after :=
  GeneralDictionarySettledRecursiveExample.stable displayChild child_generated after

/-- Nonvacuous semantic success and operational obstruction coexist.
The producer remains unsettled; this is not an inconsistency of final models. -/
theorem realized : Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSettledBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected (.node 1 [.node 3 []])) ∧
    GeneralNominalSettledSupport.Unsettled finish.current packet ∧
    Generated finish.current displayRoot displayChild ∧
    ∀ after, ¬ GeneralNominalSettledSteps.At registry finish displayChild after :=
  ⟨current_model,GeneralDictionarySettledRecursiveExample.classified,
    GeneralDictionarySettledRecursiveExample.packet_unsettled,child_generated,no_child_at⟩
end Yulang.GeneralDictionaryRecursiveConsumerObstruction
