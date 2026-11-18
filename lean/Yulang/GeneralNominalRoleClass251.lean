import Yulang.GeneralNominalRoleEffects251
import Yulang.GeneralNominalRebaseClassView243
namespace Yulang.GeneralNominalRoleClass251
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalCenters (Plan)
open GeneralNominalRebaseEffectView243 (Equation)
open GeneralNominalRebaseClassView243 (View)
open CommonNominalFullCarrier

def equations (plan : Plan roles) (env : Syntax) : List GeneralSourceState.Output → Option (List Equation)
 | [] => some []
 | output :: rest => (GeneralNominalRoleEffects251.compile plan env output).bind fun equation =>
   (equations plan env rest).map (equation :: ·)

theorem equations_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment)
 (outputs : List GeneralSourceState.Output) (result : List Equation) (success : equations plan env outputs = some result) :
 (∀ equation ∈ result, equation.Holds assignment) ↔
 ∀ output ∈ outputs, GeneralNominalRoleEffects251.OutputHolds plan (read env assignment) output := by
 induction outputs generalizing result with
 | nil => simp [equations] at success; subst result; simp
 | cons output rest ih =>
   cases head : GeneralNominalRoleEffects251.compile plan env output with
   | none => simp [equations,head] at success
   | some equation =>
     cases tail : equations plan env rest with
     | none => simp [equations,head,tail] at success
     | some resultTail =>
       simp only [equations,head,Option.bind_some,tail,Option.map_some,Option.some.injEq] at success
       subst result
       simp only [List.forall_mem_cons]
       exact and_congr (GeneralNominalRoleEffects251.compiled_exact plan env assignment output equation head) (ih resultTail tail)

def compile (plan : Plan roles) (env : Syntax) (outputs : List GeneralSourceState.Output) : Option View :=
 (equations plan env outputs).map fun generated => ⟨generated,GeneralNominalRebaseClassView243.equalities env.target outputs⟩

def Holds (plan : Plan roles) (values : Values) (outputs : List GeneralSourceState.Output) : Prop :=
 (∀ output ∈ outputs, GeneralNominalRoleEffects251.OutputHolds plan values output) ∧
 ∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name → Equivalent (values.target first.target).1 (values.target last.target).1

theorem compile_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment)
 (outputs : List GeneralSourceState.Output) (result : View) (success : compile plan env outputs = some result) :
 result.Holds assignment ↔ Holds plan (read env assignment) outputs := by
 obtain ⟨generated,found,rfl⟩ := Option.map_eq_some_iff.mp success
 exact and_congr (equations_exact plan env assignment outputs generated found)
   (GeneralNominalRebaseClassView243.equalities_exact env.target assignment outputs)

noncomputable def current (core : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (env : Syntax) : Option View :=
 compile plan env (GeneralNominalCenteredHeadOutputs.requests core plan.packet.site.occurrence)

theorem current_exact (core : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) (env : Syntax) (assignment : Assignment)
 (result : View) (success : current core plan env = some result) :
 result.Holds assignment ↔ Holds plan (read env assignment)
   (GeneralNominalCenteredHeadOutputs.requests core plan.packet.site.occurrence) :=
 compile_exact plan env assignment _ result success

theorem equations_length (plan : Plan roles) (env : Syntax) (outputs : List GeneralSourceState.Output) (result : List Equation)
 (success : equations plan env outputs = some result) : result.length = outputs.length := by
 induction outputs generalizing result with
 | nil => simp [equations] at success; subst result; rfl
 | cons output rest ih =>
   cases head : GeneralNominalRoleEffects251.compile plan env output with
   | none => simp [equations,head] at success
   | some equation =>
     cases tail : equations plan env rest with
     | none => simp [equations,head,tail] at success
     | some resultTail =>
       simp only [equations,head,Option.bind_some,tail,Option.map_some,Option.some.injEq] at success
       subst result
       exact congrArg Nat.succ (ih resultTail tail)
end Yulang.GeneralNominalRoleClass251
