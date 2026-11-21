import Yulang.GeneralMixedCompoundPointFirstPublic308
import Yulang.GeneralMixedCompoundSourceFork308
import Yulang.GeneralMixedIndexedCommit305

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralMixedCompoundInitialNonjoin308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundObstruction238 (currentPlan no_current_packet)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundPointFirstPlan308 (plan pointFirst same_plan candidateModel)
open GeneralMixedCompoundPointFirstInstall308 (point_first_held generated_child two_step)
open GeneralMixedCompoundPointFirstPublic308 (same_projection)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step steps_models)
open GeneralNominalCommonBridge (Assignment)
open GeneralMixedIndexedCommit305 (symm_same)

theorem disjoint (m : Assignment) (historical : Models installed m) : ¬ Models pointFirst m := by
  intro other
  have oldPoint := (GeneralDictionaryCompoundPoint238.models_iff m).mpr historical
  have packet := GeneralMixedCompoundPointFirstPublic308.installed_held m other
  have newer : GeneralNominalVersionedPlans231.Holds currentPlan m :=
    GeneralDeferredLadderTransport302.held_of_reindex (symm_same same_plan) m packet oldPoint.1.1
  exact no_current_packet m oldPoint newer

theorem distinct : installed ≠ pointFirst := by
  intro eq
  have same := point_first_held
  rw [← eq] at same
  exact disjoint candidateModel same point_first_held

theorem no_inhabited_join (t : State roles)
    (original : B4Target.Steps (Step registry root) installed t)
    (other : B4Target.Steps (Step registry root) pointFirst t) :
    ¬ ∃ model, Models t model := by
  rintro ⟨m,valid⟩
  exact disjoint m (steps_models original valid) (steps_models other valid)

theorem packet_models_not_a_public_observer :
    (∀ boundary, (∃ m, Agrees m boundary ∧ Models pointFirst m) ↔
      (∃ m, Agrees m boundary ∧ Models installed m)) ∧
    ∃ m, Models pointFirst m ∧ ¬ Models installed m := by
  refine ⟨same_projection,candidateModel,point_first_held,?_⟩
  exact fun h => disjoint candidateModel h point_first_held

theorem both_real_paths :
    B4Target.Steps (Step registry root) before installed ∧
    B4Target.Steps (Step registry root) before pointFirst ∧
    (∃ m, Models installed m) ∧ (∃ m, Models pointFirst m) ∧
    (∀ m, Models installed m → ¬ Models pointFirst m) :=
  ⟨.tail .refl GeneralDictionaryCompoundStep238.step,two_step,
    ⟨_,GeneralDictionaryCompoundStep238.installed_model⟩,⟨_,point_first_held⟩,disjoint⟩

end Yulang.GeneralMixedCompoundInitialNonjoin308
