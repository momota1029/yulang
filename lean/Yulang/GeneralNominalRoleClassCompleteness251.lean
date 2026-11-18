import Yulang.GeneralNominalRoleClass251
namespace Yulang.GeneralNominalRoleClassCompleteness251
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalCenters (Plan)
open GeneralNominalRebaseEffectView243 (Equation)

theorem equations_complete (plan : Plan roles) (env : Syntax) (assignment : Assignment)
 (outputs : List GeneralSourceState.Output)
 (valid : ∀ output ∈ outputs, GeneralNominalRoleEffects251.OutputHolds plan (read env assignment) output) :
 ∃ result, GeneralNominalRoleClass251.equations plan env outputs = some result ∧
 ∀ equation ∈ result, equation.Holds assignment := by
 induction outputs with
 | nil => exact ⟨[],rfl,by simp⟩
 | cons output rest ih =>
   obtain ⟨equation,head,held⟩ := (GeneralNominalRoleEffects251.output_exact plan env assignment output).mpr (valid output (by simp))
   obtain ⟨tail,compiled,validTail⟩ := ih (fun out member => valid out (List.mem_cons_of_mem _ member))
   refine ⟨equation :: tail,by simp [GeneralNominalRoleClass251.equations,head,compiled],?_⟩
   intro chosen member
   rcases List.mem_cons.mp member with rfl | present
   · exact held
   · exact validTail chosen present

theorem model_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) (outputs : List GeneralSourceState.Output) :
 (∃ result, GeneralNominalRoleClass251.compile plan env outputs = some result ∧ result.Holds assignment) ↔
 GeneralNominalRoleClass251.Holds plan (read env assignment) outputs := by
 constructor
 · rintro ⟨result,compiled,valid⟩
   exact (GeneralNominalRoleClass251.compile_exact plan env assignment outputs result compiled).mp valid
 · intro valid
   obtain ⟨generated,found,held⟩ := equations_complete plan env assignment outputs valid.1
   refine ⟨⟨generated,GeneralNominalRebaseClassView243.equalities env.target outputs⟩,?_,held,?_⟩
   · simp [GeneralNominalRoleClass251.compile,found]
   · exact (GeneralNominalRebaseClassView243.equalities_exact env.target assignment outputs).mpr valid.2
end Yulang.GeneralNominalRoleClassCompleteness251
