import Yulang.GeneralNominalRoleEquations251
namespace Yulang.GeneralNominalRoleEffects251
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalCenters (Plan)
open GeneralNominalMaterialization (Mode)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup)
open GeneralNominalRebaseEffectView243 (Equation)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier

def variables (plan : Plan roles) (env : Syntax) : Body → Mode → Nat → TyTerm Nat
 | .explicit _ => GeneralNominalRoleEnvironment251.variables plan.packet.declaration.outputNames env
 | .default _ _ _ => GeneralNominalRoleEquations251.positional env (List.ofFn plan.input.center)

def values (plan : Plan roles) (env : Values) : Body → Mode → Nat → Ty
 | .explicit _ => env.variables plan.packet.declaration.outputNames
 | .default _ _ _ => GeneralNominalRoleEquations251.Values.positional env (List.ofFn plan.input.center)

theorem variables_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) (body : Body) :
 (fun mode name => (variables plan env body mode name).eval model assignment) = values plan (read env assignment) body := by
 funext mode name
 cases body with
 | explicit => exact GeneralNominalRoleEnvironment251.variables_exact _ _ _ _ _
 | default => rfl

def compileBody (plan : Plan roles) (env : Syntax) (target : Nat) (body : Body) : Option Equation :=
 (GeneralNominalCenteredHeadMatEffects.compileBody plan body).map fun expression =>
 ⟨(env.target target).ty,GeneralNominalRebaseEffectView243.compile (variables plan env body) .actual expression⟩

def OutputHolds (plan : Plan roles) (env : Values) (output : GeneralSourceState.Output) : Prop :=
 ∃ body, Supplies roles plan.packet.declaration output.name body ∧
 ∃ expression, GeneralNominalCenteredHeadMatEffects.compileBody plan body = some expression ∧
 Equivalent (env.target output.target).1 (value (values plan env body) .actual expression)

def compile (plan : Plan roles) (env : Syntax) (output : GeneralSourceState.Output) : Option Equation :=
 (lookup roles plan.packet.declaration output.name).bind (compileBody plan env output.target)

theorem output_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) (output : GeneralSourceState.Output) :
 (∃ equation, compile plan env output = some equation ∧ equation.Holds assignment) ↔ OutputHolds plan (read env assignment) output := by
 have sourceExact := GeneralDictionaryAssociatedProvenance.lookup_exact roles plan.packet.declaration
   plan.packet.checked.identified.2.2.1 output.name
 constructor
 · rintro ⟨equation,compiled,held⟩
   obtain ⟨body,found,translated⟩ := Option.bind_eq_some_iff.mp compiled
   obtain ⟨expression,translation,rfl⟩ := Option.map_eq_some_iff.mp translated
   refine ⟨body,(sourceExact body).mp found,expression,translation,?_⟩
   unfold Equation.Holds at held
   rw [GeneralNominalRebaseEffectView243.compile_exact,variables_exact] at held
   exact held
 · rintro ⟨body,supplied,expression,translation,held⟩
   refine ⟨⟨(env.target output.target).ty,GeneralNominalRebaseEffectView243.compile (variables plan env body) .actual expression⟩,?_,?_⟩
   · simp [compile,(sourceExact body).mpr supplied,compileBody,translation]
   · unfold Equation.Holds
     rw [GeneralNominalRebaseEffectView243.compile_exact,variables_exact]
     exact held

theorem compiled_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) (output : GeneralSourceState.Output)
 (equation : Equation) (success : compile plan env output = some equation) :
 equation.Holds assignment ↔ OutputHolds plan (read env assignment) output := by
 constructor
 · intro held; exact (output_exact plan env assignment output).mp ⟨equation,success,held⟩
 · intro held
   obtain ⟨other,found,valid⟩ := (output_exact plan env assignment output).mpr held
   have equal := Option.some.inj (success.symm.trans found)
   exact equal.symm ▸ valid
end Yulang.GeneralNominalRoleEffects251
