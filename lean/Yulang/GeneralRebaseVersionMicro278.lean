import Yulang.GeneralRebaseRoundMicro278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseVersionMicro278
open GeneralRebaseRoundMicro278 (Phase Tick next fired)
open GeneralDictionaryVersionLoopSource237 (roles registry root snapshot)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (allocations reservations atoms plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step step_models)
open GeneralVersionBoundaryCompletion259 (Agree complete agrees all_stages)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev installed (n : Nat) : State roles :=
  GeneralDictionaryVersionLoopInstall239.installed (stages n).shape

noncomputable abbrev refreshed (n : Nat) : State roles :=
  GeneralDictionaryVersionLoopRound239.refreshed (stages n).shape

noncomputable def raw : Tick → State roles
  | ⟨n,.enter⟩ => state n
  | ⟨n,.installed⟩ => installed n
  | ⟨n,.refreshed⟩ => refreshed n

theorem install_step (n : Nat) : Step registry root (state n) (installed n) :=
  GeneralDictionaryVersionLoopInstall239.step (stages n).shape (stages n).valid (stages n).recorded
    (GeneralDictionaryVersionLoopStage239.novel (stages n))

theorem refresh_step (n : Nat) : Step registry root (installed n) (refreshed n) :=
  GeneralDictionaryVersionLoopFamilyRefresh238.step allocations reservations atoms (installed n) n
    (stages n).shape.source rfl
    (GeneralDictionaryVersionLoopInstall239.installed_recorded (stages n).shape (stages n).recorded)

theorem reobserve_step (n : Nat) : Step registry root (refreshed n) (state (n+1)) :=
  GeneralDictionaryVersionLoopFamilyReobserve238.step allocations reservations atoms (installed n) n
    (stages n).shape.source
    (GeneralDictionaryVersionLoopInstall239.installed_recorded (stages n).shape (stages n).recorded)

theorem actual (t : Tick) : Step registry root (raw t) (raw (next t)) := by
  rcases t with ⟨n,p⟩
  cases p
  · exact install_step n
  · exact refresh_step n
  · exact reobserve_step n

theorem restrict (t : Tick) (m : Assignment) (valid : Models (raw t) m) : Models (state t.round) m := by
  rcases t with ⟨n,p⟩
  cases p
  · exact valid
  · exact step_models (install_step n) valid
  · exact step_models (install_step n) (step_models (refresh_step n) valid)

theorem complete_all (t : Tick) (boundaryData : Assignment)
    (start : GeneralNominalState.Models snapshot boundaryData) : Models (raw t) (complete boundaryData) := by
  rcases t with ⟨n,p⟩
  cases p
  · exact all_stages boundaryData start n
  · exact step_models (refresh_step n) (step_models (reobserve_step n) (all_stages boundaryData start (n+1)))
  · exact step_models (reobserve_step n) (all_stages boundaryData start (n+1))

theorem exact_public (t : Tick) (boundaryData : Assignment) :
    (∃ m, Agree m boundaryData ∧ Models (raw t) m) ↔ GeneralNominalState.Models snapshot boundaryData :=
  GeneralRebaseRoundMicro278.sandwich Agree (GeneralNominalState.Models snapshot)
    (Models (state t.round)) (Models (raw t)) (restrict t)
    (GeneralVersionPublicProjection259.stage_models t.round) complete agrees
    (fun p source => complete_all t p source) boundaryData

theorem simultaneous_public (boundaryData : Assignment) :
    (∃ m, Agree m boundaryData ∧ ∀ t, Models (raw t) m) ↔ GeneralNominalState.Models snapshot boundaryData := by
  constructor
  · rintro ⟨m,agrees,all⟩
    exact (exact_public ⟨0,.enter⟩ boundaryData).mp ⟨m,agrees,all ⟨0,.enter⟩⟩
  · intro start
    exact ⟨complete boundaryData,agrees boundaryData,fun t => complete_all t boundaryData start⟩

def normalized (t : Tick) : GeneralRebaseStep258.State GeneralVersionRebaseStep259.facts :=
  if fired t then GeneralVersionRebaseStep259.finalState else GeneralVersionRebaseStep259.initialState

theorem joint_model (t : Tick) (boundaryData : Assignment) (valid : GeneralNominalState.Models snapshot boundaryData) :
    Models (raw t) (complete boundaryData) ∧ GeneralVersionRebaseModels259.Models (normalized t) (complete boundaryData) := by
  refine ⟨complete_all t boundaryData valid,?_⟩
  unfold normalized
  split
  · exact GeneralVersionRebaseModels259.completed _ boundaryData valid
  · exact GeneralVersionRebaseModels259.completed _ boundaryData valid

theorem simulate (t : Tick) :
    GeneralVersionRebaseStep259.run (normalized t) = some (normalized (next t)) ∨
      (GeneralVersionRebaseStep259.run (normalized t) = none ∧ normalized (next t) = normalized t) := by
  simp only [normalized,GeneralRebaseRoundMicro278.next_fired,ite_true]
  cases done : fired t
  · left; simpa [done] using GeneralVersionRebaseStep259.run_first
  · right; simpa [done] using GeneralVersionRebaseStep259.run_stop

end Yulang.GeneralRebaseVersionMicro278
