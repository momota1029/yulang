import Yulang.GeneralDictionarySourceExtension258
namespace Yulang.GeneralDictionaryPrivateBoundary258
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryBinderGap257 (seed)
open GeneralDictionaryInitialFill258 (complete)
open CommonNominalFullCarrier

theorem seed_not_binder : ¬ GeneralDictionaryBinderFact257.Holds seed := by
 intro binder
 exact GeneralDictionaryBinderFact257.excludes_gap 0
   ((GeneralDictionaryFiniteJournal257.solve_binder 1 seed).mpr binder)

theorem complete_holds (assignment : Assignment) : GeneralDictionaryBinderFact257.Holds (complete assignment) :=
 (GeneralDictionaryUniformView258.binder_exact (GeneralDictionaryInitialFill258.bind assignment)).mpr
   (GeneralDictionaryInitialFill258.binder assignment)

theorem changes_seed : complete seed ≠ seed := by
 intro equal
 have holds := complete_holds seed
 rw [equal] at holds
 exact seed_not_binder holds

theorem seed_extended :
 GeneralDictionaryInitialProjection257.Agree (complete seed) seed ∧
 ∀ n, GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n) (complete seed) := by
 refine ⟨GeneralDictionaryInitialFill258.public_agrees seed,?_⟩
 apply (GeneralDictionaryInitialFill258.all_stages seed).mpr
 exact ((GeneralNominalVersionedJournal232.initial_models ..).mp GeneralDictionaryBinderGap257.seed_models).1

/-- The stronger boundary retaining the actual binder cannot extend this
initial model. Source-boundary extension above intentionally releases it. -/
theorem retained_binder_impossible (n : Nat) :
 ¬ ∃ assignment, GeneralDictionaryFiniteJournal257.Agree assignment seed ∧
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) assignment := by
 rintro ⟨assignment,same,valid⟩
 have binder := (GeneralDictionaryJournalRepair257.exact n assignment).mp valid |>.2
 have actual := same.1 GeneralDictionaryLooseLoopPacket240.actual (Or.inr rfl)
 have two := same.1 2 (Or.inl (by decide))
 unfold GeneralDictionaryBinderFact257.Holds at binder
 rw [actual,two] at binder
 exact seed_not_binder binder
end Yulang.GeneralDictionaryPrivateBoundary258
