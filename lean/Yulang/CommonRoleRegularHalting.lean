import Yulang.CommonRoleRegularRegistry
import Yulang.CommonRoleLinearExecution

/-! Exact finite role resolution and dictionary existence for the concrete
checked registry compiled from each finite program. No safety, termination,
associated determination or successful-resolution premise remains. -/

namespace Yulang.CommonRoleRegularHalting

open CommonRoleComputation (Code Tree Halts)
open CommonRoleLinearClock
open CommonRoleLinearEvidence
open CommonRoleLinearProgram (rules)
open CommonRoleLinearExecution (RawHalts)
open CommonRoleRegularRegistry

def start (code : Code) (input : Tree) : Configuration :=
  (CommonRoleLinearInterpreter.State.run code input .halt).encode

def goal (code : Code) (input : Tree) : SemanticGoal := goalOf (start code input)

theorem machine_iff_raw (code : Code) (configuration : Configuration) :
    MachineHalts (registry code) 0 configuration ↔ RawHalts code configuration := by
  constructor
  · intro halting
    induction halting with
    | done finished => exact .done finished
    | step entry member transition _ ih =>
        exact .step ⟨entry.2, ((mem_registry code entry).mp member).1, transition⟩ ih
  · intro halting
    induction halting with
    | done finished => exact .done finished
    | step transition _ ih =>
        obtain ⟨rule, member, step⟩ := transition
        exact .step ((rules code).idxOf rule, rule)
          ((mem_registry code _).mpr ⟨member, rfl⟩) step ih

theorem machine_halts_exact (code : Code) (input : Tree) :
    MachineHalts (registry code) 0 (start code input) ↔ Halts code input :=
  (machine_iff_raw code _).trans (CommonRoleLinearExecution.halts_exact code input)

theorem derives_exact (code : Code) (input : Tree) :
    Derives (registry code) 0 (goal code input) ↔ Halts code input :=
  (derives_iff_machine_halts _ _ (registry_linear code) _).trans (machine_halts_exact code input)

theorem resolves_exact (code : Code) (input : Tree) :
    Resolves (registry code) 0 (goal code input) ↔ Halts code input :=
  (resolves_iff_machine_halts _ _ (registry_linear code) _ (registry_safe code _)).trans
    (machine_halts_exact code input)

theorem dictionary_exact (code : Code) (input : Tree) :
    Nonempty (Dictionary (registry code) 0 (goal code input)) ↔ Halts code input :=
  (dictionary_iff_machine_halts _ _ (registry_linear code) _ (registry_safe code _)).trans
    (machine_halts_exact code input)

theorem no_ambiguity (code : Code) (input : Tree) :
    ¬ ReachesOverlap (registry code) 0 (goal code input) :=
  no_reachable_overlap (registry_linear code) (registry_safe code _)

/-- Actual complete dictionary plans, including every recursive child, use
only this one visible registry. The plan is not merely a role-head demand. -/
theorem actual_plan_exact (code : Code) (input : Tree) :
    (∃ dictionary : Dictionary (registry code) 0 (goal code input),
      ∀ implementation ∈ dictionary.erase.declarations,
        implementation ∈ visible (registry code) 0) ↔ Halts code input := by
  constructor
  · rintro ⟨dictionary, _⟩
    exact (dictionary_exact code input).mp ⟨dictionary⟩
  · intro halting
    obtain ⟨dictionary⟩ := (dictionary_exact code input).mpr halting
    exact ⟨dictionary, dictionary.all_visible⟩

end Yulang.CommonRoleRegularHalting
