import Yulang.GeneralMixedCompoundPointPorts308
import Yulang.GeneralMixedCompoundInitialNonjoin308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralMixedCompoundPointFeedback308
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralRebaseCompoundReplacement273 (lower upper)
open GeneralMixedCompoundPointFirstPlan308 (pointFirst candidateModel)
open GeneralMixedCompoundPointFirstInstall308 (point_first_held generated_child)
open GeneralMixedCompoundPointPorts308 (afterSnap lower_reserved upper_reserved lower_not_read equal old_not_equal)
open GeneralNominalVersionedMixedKernel234 (Step Administrative Equal)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalFeedbackSteps (RawEqual)

def putTop (m : Assignment) : Assignment := fun n => if n = lower then (.top,(m n).2) else m n

theorem distinct : lower ≠ upper := by decide +kernel

theorem raw_gap : ¬ RawEqual pointFirst.core.erased.current lower upper := by
  intro raw
  have initial : GeneralNominalState.Models afterSnap candidateModel := point_first_held.1.1
  have changed : GeneralNominalState.Models afterSnap (putTop candidateModel) :=
    (GeneralDictionaryDefaultRawSupport213.models_iff _ (fun n hn => by
      have different : n ≠ lower := fun e => lower_not_read (e ▸ hn)
      rw [putTop,ite_eq_right different])).mp initial
  have clash := raw (putTop candidateModel) changed
  simp only [putTop,ite_true,ite_eq_right distinct.symm] at clash
  change Equivalent .top (GeneralRebaseCompoundReplacement273.patch GeneralDictionaryCompoundPointModel238.extended upper).1 at clash
  rw [GeneralRebaseCompoundReplacement273.upper_value] at clash
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head _
    (GeneralNominalOriginCongruence238.test_iff clash (.structural (.variant 0)) |>.mpr
      ⟨[.emptyRecord],rfl,subtype_refl _,subtype_refl _⟩)

theorem port_sources : lower ∈ GeneralNominalState.sources afterSnap ∧
    upper ∈ GeneralNominalState.sources afterSnap := by
  simp only [GeneralNominalState.sources,List.mem_append]
  exact ⟨Or.inl (Or.inr lower_reserved),Or.inl (Or.inr upper_reserved)⟩

def Enabled (s : State roles) : Prop :=
  lower ∈ GeneralNominalState.sources s.core.erased.current.context.state ∧
  upper ∈ GeneralNominalState.sources s.core.erased.current.context.state ∧
  Equal s lower upper ∧ ¬ RawEqual s.core.erased.current lower upper

theorem point_enabled : Enabled pointFirst := ⟨port_sources.1,port_sources.2,equal,raw_gap⟩
theorem old_disabled : ¬ Enabled installed := fun h => old_not_equal h.2.2.1

noncomputable abbrev withFeedback :=
  GeneralNominalVersionedAdministrative232.equate pointFirst lower upper

theorem step : Step registry root pointFirst withFeedback :=
 ⟨root,.root,.administrative (.equate root lower upper port_sources.1 port_sources.2 equal raw_gap)⟩

theorem models_iff (m : Assignment) : Models withFeedback m ↔ Models pointFirst m :=
 GeneralNominalVersionedMixedEqualityClosure235.equate_models_iff equal m

theorem learned : RawEqual withFeedback.core.erased.current lower upper :=
 GeneralNominalFeedbackSteps.equate_feedback _ _ _

theorem not_repeat : ¬ Enabled withFeedback := fun h => h.2.2.2 learned

theorem public_projection_not_feedback :
  (∀ boundary, (∃ m, GeneralRebaseCompoundRows273.Agrees m boundary ∧ Models pointFirst m) ↔
    (∃ m, GeneralRebaseCompoundRows273.Agrees m boundary ∧ Models installed m)) ∧
  Enabled pointFirst ∧ ¬ Enabled installed ∧ Step registry root pointFirst withFeedback :=
  ⟨GeneralMixedCompoundPointFirstPublic308.same_projection,point_enabled,old_disabled,step⟩

end Yulang.GeneralMixedCompoundPointFeedback308
