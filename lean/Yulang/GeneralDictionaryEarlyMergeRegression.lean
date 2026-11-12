import Yulang.GeneralDictionaryEarlyMergeChoices
import Yulang.GeneralDictionarySupportRevisionObstruction

/-! Actual support installation and certified reobservation are admitted by the
structural schedule. Coherence does not imply the false literal Current claim.
This trace contains no merge; it checks the unrestricted administrative case,
not that the current executor always performs early merges. -/
namespace Yulang.GeneralDictionaryEarlyMergeRegression
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState
open GeneralDictionarySupportRevisionObstruction GeneralDictionaryEarlyMergeChoices

theorem scheduled : Scheduled registry root finish := by
  have installed : Scheduled registry root trackedInstalled := by
    refine .install (.initial context initial_source) packet [] .root
      GeneralNominalFeedbackRegressions.enabled ?_ packet_guard
    intro committed
    have absent := committed.2 child (by rw [children_exact]; simp)
    cases absent
  exact .administrative installed root .root (.reobserve root
    GeneralDictionaryCurrentRevisionObstruction.revision
    GeneralDictionaryCurrentRevisionObstruction.certified
    GeneralDictionaryCurrentRevisionObstruction.improves)

/-- A real, inhabited, nonempty support journal may have coherent recorded keys
without admitting literal reinterpretation of every packet in current context. -/
theorem coherent_not_current :
    GeneralDictionarySupportChoices.Coherent finish.current ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧
    ¬ GeneralDictionaryCurrentJournal.Current registry finish.current :=
  ⟨scheduled_coherent registry root finish scheduled,modeled_nonempty.1,
    modeled_nonempty.2,not_current⟩

end Yulang.GeneralDictionaryEarlyMergeRegression
