import Yulang.GeneralDictionaryRebaseStep258
namespace Yulang.GeneralDictionaryRebasePublic258
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInitialProjection257 (Agree)
open GeneralDictionaryRebaseStep258
/-- Only the initial/done states are reachable from this fixture. Intermediate
subsets are not assigned an alleged general-language semantics. -/
def Models (state : GeneralRebaseStep258.State facts) (assignment : Assignment) : Prop :=
 if state.remaining = facts then (GeneralDictionaryFiveSlot257.view 0).Models assignment
 else (GeneralDictionaryFiniteJournal257.view 1).Models assignment

theorem initial_exact (assignment : Assignment) : Models initialState assignment ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment := by
 simpa only [Models,GeneralRebaseStep258.initial,ite_true] using GeneralDictionaryInitialFill258.raw_initial assignment

theorem final_exact (assignment : Assignment) : Models finalState assignment ↔
 (GeneralDictionaryFiniteJournal257.view 1).Models assignment := by rfl

theorem final_public (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models finalState assignment) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   have small := ((GeneralDictionaryFiniteJournal257.models_exact 1 assignment).mp valid).1
   have start := (GeneralDictionaryNoModelRefinement257.all_iff_zero 1 assignment).mp small
   exact (GeneralDictionaryInitialFill258.raw_initial boundary).mp
     ((GeneralDictionarySourceExtension258.view_agree 0 assignment boundary same).mp start)
 · intro source
   refine ⟨GeneralDictionaryInitialFill258.bind boundary, ?_, ?_⟩
   · exact ⟨GeneralDictionaryInitialFill258.initial boundary,GeneralDictionaryInitialFill258.rows boundary⟩
   · apply (final_exact _).mpr
     apply (GeneralDictionaryFiniteJournal257.models_exact 1 _).mpr
     refine ⟨?_,GeneralDictionaryInitialFill258.binder boundary⟩
     apply (GeneralDictionaryInitialFill258.view_exact 1 boundary).mpr
     apply (GeneralDictionaryNoModelRefinement257.all_iff_zero 1 boundary).mpr
     exact (GeneralDictionaryInitialFill258.raw_initial boundary).mpr source

theorem projected_public (n : Nat) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models (project n) assignment) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary := by
 cases n with
 | zero =>
   simp only [project,ite_true,initial_exact]
   constructor
   · rintro ⟨assignment,same,valid⟩
     exact (GeneralDictionaryInitialFill258.raw_initial boundary).mp
       ((GeneralDictionarySourceExtension258.view_agree 0 assignment boundary same).mp
         ((GeneralDictionaryInitialFill258.raw_initial assignment).mpr valid))
   · intro valid; exact ⟨boundary,⟨fun _ _ => rfl,fun _ => rfl⟩,valid⟩
 | succ n => simpa only [old_positive_project] using final_public boundary

/-- Public-model correspondence for completed I45 stages only. This is not
simulation of every old administrative step or a general source theorem. -/
theorem old_new (n : Nat) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n) assignment) ↔
 (∃ assignment, Agree assignment boundary ∧ Models (project n) assignment) :=
 (GeneralDictionarySourceExtension258.stage_models n boundary).trans (projected_public n boundary).symm
end Yulang.GeneralDictionaryRebasePublic258
