import Yulang.GeneralRebaseRoundMicro278

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26500
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseLooseMicro278
open GeneralRebaseRoundMicro278 (Phase Tick next fired)
open GeneralDictionaryLooseLoopSource240 (roles registry root snapshot)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseIterationBook240 (allocations reservations atoms plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step step_models)
open GeneralDictionaryInitialFill258 (complete public_agrees all_stages)
open GeneralDictionaryInitialProjection257 (Agree)
open GeneralNominalCommonBridge (Assignment)

abbrev PointStep := GeneralNominalPointKernel240.Step registry root

noncomputable abbrev installed (n : Nat) : State roles :=
  GeneralDictionaryLooseIterationInstall240.installed (stages n).shape

noncomputable abbrev refreshed (n : Nat) : State roles :=
  GeneralDictionaryLooseIterationRound240.refreshed (stages n).shape

noncomputable def raw : Tick → State roles
  | ⟨n,.enter⟩ => state n
  | ⟨n,.installed⟩ => installed n
  | ⟨n,.refreshed⟩ => refreshed n

theorem install_step (n : Nat) : PointStep (state n) (installed n) :=
  GeneralDictionaryLooseIterationInstall240.step (stages n).shape (stages n).valid (stages n).recorded
    (GeneralDictionaryLooseIterationStage240.novel (stages n))

theorem refresh_step (n : Nat) : PointStep (installed n) (refreshed n) :=
  GeneralDictionaryLooseFamilyRefresh240.step allocations reservations atoms (installed n) n
    (stages n).shape.source rfl
    (GeneralDictionaryLooseIterationInstall240.installed_recorded (stages n).shape (stages n).recorded)

theorem reobserve_step (n : Nat) : PointStep (refreshed n) (state (n+1)) :=
  GeneralDictionaryLooseFamilyReobserve240.step allocations reservations atoms (installed n) n
    (stages n).shape.source
    (GeneralDictionaryLooseIterationInstall240.installed_recorded (stages n).shape (stages n).recorded)

theorem point_actual (t : Tick) : PointStep (raw t) (raw (next t)) := by
  rcases t with ⟨n,p⟩
  cases p
  · exact install_step n
  · exact refresh_step n
  · exact reobserve_step n

theorem actual (t : Tick) : Step registry root (raw t) (raw (next t)) :=
  GeneralNominalPointErasure240.step_old (point_actual t)

theorem point_models {a b : State roles} {m : Assignment} (edge : PointStep a b) (held : Models b m) :
    Models a m := step_models (GeneralNominalPointErasure240.step_old edge) held

theorem restrict (t : Tick) (m : Assignment) (valid : Models (raw t) m) : Models (state t.round) m := by
  rcases t with ⟨n,p⟩
  cases p
  · exact valid
  · exact point_models (install_step n) valid
  · exact point_models (install_step n) (point_models (refresh_step n) valid)

theorem complete_all (t : Tick) (boundaryData : Assignment)
    (start : GeneralNominalState.Models snapshot boundaryData) : Models (raw t) (complete boundaryData) := by
  rcases t with ⟨n,p⟩
  have witnesses := (all_stages boundaryData).mpr start
  cases p
  · exact witnesses n
  · exact point_models (refresh_step n) (point_models (reobserve_step n) (witnesses (n+1)))
  · exact point_models (reobserve_step n) (witnesses (n+1))

theorem exact_public (t : Tick) (boundaryData : Assignment) :
    (∃ m, Agree m boundaryData ∧ Models (raw t) m) ↔ GeneralNominalState.Models snapshot boundaryData :=
  GeneralRebaseRoundMicro278.sandwich Agree (GeneralNominalState.Models snapshot)
    (Models (state t.round)) (Models (raw t)) (restrict t)
    (GeneralDictionarySourceExtension258.stage_models t.round) complete public_agrees
    (fun p source => complete_all t p source) boundaryData

theorem simultaneous_public (boundaryData : Assignment) :
    (∃ m, Agree m boundaryData ∧ ∀ t, Models (raw t) m) ↔ GeneralNominalState.Models snapshot boundaryData := by
  constructor
  · rintro ⟨m,agrees,all⟩
    exact (exact_public ⟨0,.enter⟩ boundaryData).mp ⟨m,agrees,all ⟨0,.enter⟩⟩
  · intro start
    exact ⟨complete boundaryData,public_agrees boundaryData,fun t => complete_all t boundaryData start⟩

def normalized (t : Tick) : GeneralRebaseStep258.State GeneralDictionaryRebaseStep258.facts :=
  if fired t then GeneralDictionaryRebaseStep258.finalState else GeneralDictionaryRebaseStep258.initialState

theorem joint_model (t : Tick) (boundaryData : Assignment) (valid : GeneralNominalState.Models snapshot boundaryData) :
    Models (raw t) (complete boundaryData) ∧ GeneralDictionaryRebasePublic258.Models (normalized t) (complete boundaryData) := by
  refine ⟨complete_all t boundaryData valid,?_⟩
  unfold normalized
  split
  · exact (GeneralDictionaryRebaseCertificate259.certificate t.round boundaryData valid).final
  · exact (GeneralDictionaryRebasePublic258.initial_exact _).mpr
      ((GeneralNominalVersionedJournal232.initial_models _ _ _).mp ((all_stages boundaryData).mpr valid 0)).1

theorem simulate (t : Tick) :
    GeneralDictionaryRebaseRun259.run t.round (normalized t) = some (normalized (next t)) ∨
      (GeneralDictionaryRebaseRun259.run t.round (normalized t) = none ∧ normalized (next t) = normalized t) := by
  simp only [normalized,GeneralRebaseRoundMicro278.next_fired,ite_true]
  cases done : fired t
  · left; simpa [done] using GeneralDictionaryRebaseRun259.initial_runs t.round
  · right; simpa [done] using GeneralDictionaryRebaseRun259.final_noop t.round

end Yulang.GeneralRebaseLooseMicro278
