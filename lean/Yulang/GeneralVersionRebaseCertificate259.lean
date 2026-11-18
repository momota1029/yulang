import Yulang.GeneralVersionRebaseModels259
namespace Yulang.GeneralVersionRebaseCertificate259
open GeneralRebaseStep258
open GeneralVersionRebaseStep259 (facts initialState finalState run)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionBoundaryCompletion259 (complete Agree)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (plan)

def project (n : Nat) : State facts := if n = 0 then initialState else finalState

structure Certificate (n : Nat) (boundary : Assignment) : Prop where
 agrees : Agree (complete boundary) boundary
 current : GeneralNominalVersionedJournal232.Models (state n) (complete boundary)
 packet : GeneralNominalVersionedPlans231.Holds (plan n) (complete boundary)
 next : GeneralNominalVersionedJournal232.Models (state (n+1)) (complete boundary)
 final : GeneralVersionRebaseModels259.Models finalState (complete boundary)

theorem certificate (n : Nat) (boundary : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryVersionLoopSource237.snapshot boundary) : Certificate n boundary :=
 ⟨GeneralVersionBoundaryCompletion259.agrees boundary,
 GeneralVersionBoundaryCompletion259.all_stages boundary source n,
 GeneralVersionBoundaryCompletion259.packet_holds boundary source n,
 GeneralVersionBoundaryCompletion259.all_stages boundary source (n+1),
 GeneralVersionRebaseModels259.completed finalState boundary source⟩

theorem old_new (n : Nat) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ GeneralNominalVersionedJournal232.Models (state n) assignment) ↔
 (∃ assignment, Agree assignment boundary ∧ GeneralVersionRebaseModels259.Models (project n) assignment) :=
 (GeneralVersionPublicProjection259.stage_models n boundary).trans
   (GeneralVersionRebaseModels259.public_models (project n) boundary).symm

theorem run_certificate (n : Nat) (boundary : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryVersionLoopSource237.snapshot boundary) :
 run initialState = some finalState ∧ Certificate n boundary :=
 ⟨GeneralVersionRebaseStep259.run_first,certificate n boundary source⟩

/-- Complete old rounds stutter after the initial installation. This does not
simulate each administrative microstep or define a general source compiler. -/
theorem completed_round_simulation (n : Nat) :
 run (project n) = some (project (n+1)) ∨
 (run (project n) = none ∧ project (n+1) = project n) := by
 cases n with
 | zero => left; exact GeneralVersionRebaseStep259.run_first
 | succ n =>
   right
   have one : project (n+1) = finalState := by simp [project]
   have two : project (n+1+1) = finalState := by simp [project]
   rw [one,two]
   exact ⟨GeneralVersionRebaseStep259.run_stop,rfl⟩

/-- The old freshness-based semantic novelty remains true; the new normalized
fact installation is already done. This is not a rejected source program. -/
theorem old_novel_new_noop (n : Nat) :
 ¬ GeneralNominalVersionedKernel232.Committed (state n) (plan n) ∧ run finalState = none :=
 ⟨GeneralDictionaryVersionLoopStage239.novel (stages n),GeneralVersionRebaseStep259.run_stop⟩
end Yulang.GeneralVersionRebaseCertificate259
