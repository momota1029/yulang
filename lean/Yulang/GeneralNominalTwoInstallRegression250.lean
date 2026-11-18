import Yulang.GeneralNominalCoverageRegression250
/-! Two installs reuse one target while preserving both stages' obligations.
Old consumers are expanded before that target changes. Keeping the old consumer
literal would incorrectly equate distinct public types in this finite example. -/
namespace Yulang.GeneralNominalTwoInstallRegression250
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244
open GeneralNominalMaterializedOwnerFrame249 (Frame Models)
open GeneralNominalJournalAppend250 (Delta)
open GeneralNominalFiniteInstallTrace250 (Command advance run)
open GeneralNominalPostInstallRegression250 (frame empty_journal_models)
open CommonNominalFullCarrier

def firstDelta : Delta := ⟨[],[],[],[],equations 2 (.var 0)⟩
def lastDelta : Delta := ⟨[],[],[],[],equations 2 (.var 1)⟩
def first : Command := ⟨[(2,.var 0)],firstDelta⟩
def last : Command := ⟨[(2,.var 1)],lastDelta⟩
def finalFrame : Frame := run frame [first,last]
def assignment : Assignment := fun name => (if name = 0 then model.exactEmpty else .emptyRecord,Common.rowEmpty)

theorem checked_success : GeneralNominalCheckedInstall250.run frame [first,last] = some finalFrame := rfl

theorem fixed_domain : finalFrame.definitions.map Prod.fst = [2] := rfl

theorem accumulated_consumers : finalFrame.consumers =
 [.tyLe (.var 0) (.var 0),.tyLe (.var 0) (.var 0),.tyLe (.var 2) (.var 1),.tyLe (.var 1) (.var 2)] := rfl

theorem last_definition : finalFrame.definitions = [(2,.var 1)] := rfl

theorem all_obligations_satisfied : Models finalFrame assignment := by
 constructor
 · change (GeneralNominalJournalSubst249.subst _ (GeneralNominalJournalSubst249.subst _
     GeneralNominalPostInstallRegression250.emptyJournal)).Models assignment
   rw [GeneralNominalJournalSubst249.models_exact,GeneralNominalJournalSubst249.models_exact]
   exact empty_journal_models _
 · change All model assignment (finalFrame.consumers ++ block finalFrame.definitions)
   rw [accumulated_consumers,last_definition]
   intro atom member
   simp only [block,equations,List.flatMap_cons,List.flatMap_nil,List.append_nil,
     List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with (rfl | rfl | rfl | rfl) | (rfl | rfl)
   all_goals exact subtype_refl _

theorem stale_consumer_impossible :
 ¬ ∃ modelAssignment, All model modelAssignment (firstDelta.ordinary ++ lastDelta.ordinary) ∧
   modelAssignment 0 = assignment 0 ∧ modelAssignment 1 = assignment 1 := by
 rintro ⟨a,valid,zero,one⟩
 have toOld : Subtype (a 2).1 (a 0).1 :=
   valid (.tyLe (.var 2) (.var 0)) (by simp [firstDelta,lastDelta,equations])
 have fromNew : Subtype (a 1).1 (a 2).1 :=
   valid (.tyLe (.var 1) (.var 2)) (by simp [firstDelta,lastDelta,equations])
 have impossible := subtype_trans fromNew toOld
 rw [zero,one] at impossible
 exact width_not_below_exactEmpty impossible
end Yulang.GeneralNominalTwoInstallRegression250
