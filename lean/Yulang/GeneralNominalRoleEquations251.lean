import Yulang.GeneralNominalRoleSchema251
import Yulang.GeneralNominalSchemaCongruence238
/-! Target values, actual binders and aggregate mode variables are independent.
Nominal children retain actual mode through the existing total expression compiler. -/
namespace Yulang.GeneralNominalRoleEquations251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalMaterialization (Mode)
open GeneralNominalRebaseEffectView243 (Equation)
open GeneralNominalCenteredHeadMatSchemas (Schema)
open CommonNominalFullCarrier

def equation (outputs : List Nat) (env : Syntax) (source : GeneralNominalCenteredHeadMatSchemas.Equation) : Equation :=
 ⟨(env.target source.target).ty,
 GeneralNominalRebaseEffectView243.compile (variables outputs env) source.mode source.expression⟩

def compile (outputs : List Nat) (env : Syntax) (schema : Schema) : List Equation :=
 schema.equations.map (equation outputs env)

theorem equation_exact (outputs : List Nat) (env : Syntax) (assignment : Assignment)
 (source : GeneralNominalCenteredHeadMatSchemas.Equation) :
 (equation outputs env source).Holds assignment ↔
 source.Holds ((read env assignment).variables outputs) (read env assignment).target := by
 unfold equation Equation.Holds GeneralNominalCenteredHeadMatSchemas.Equation.Holds
 rw [GeneralNominalRebaseEffectView243.compile_exact]
 have equal : (fun mode name => (variables outputs env mode name).eval model assignment) =
   (read env assignment).variables outputs := funext fun mode => funext fun name => variables_exact outputs env assignment mode name
 rw [equal]
 rfl

theorem compile_exact (outputs : List Nat) (env : Syntax) (assignment : Assignment) (schema : Schema) :
 GeneralNominalRebasePacketView243.AllEquations (compile outputs env schema) assignment ↔
 schema.Holds ((read env assignment).variables outputs) (read env assignment).target := by
 simp only [compile,GeneralNominalRebasePacketView243.AllEquations,Schema.Holds,List.forall_mem_map,equation_exact]

theorem schema_related (same : Related first last) (outputs : List Nat) (schema : Schema) :
 schema.Holds (first.variables outputs) first.target ↔ schema.Holds (last.variables outputs) last.target :=
 GeneralNominalSchemaCongruence238.total_schema_iff same.target _ _ (variables_related same outputs) schema

/-- Defaults use input positions, not declaration variable names. -/
def positional (env : Syntax) (centers : List Nat) (_mode : Mode) (position : Nat) : TyTerm Nat :=
 (env.old (centers[position]?.getD 0)).ty

def Values.positional (values : Values) (centers : List Nat) (_mode : Mode) (position : Nat) : Ty :=
 (values.old (centers[position]?.getD 0)).1

theorem positional_exact (env : Syntax) (assignment : Assignment) (centers : List Nat) (mode : Mode) (position : Nat) :
 (positional env centers mode position).eval model assignment = Values.positional (read env assignment) centers mode position := rfl

def defaultEquation (env : Syntax) (centers : List Nat) (source : GeneralNominalCenteredHeadMatSchemas.Equation) : Equation :=
 ⟨(env.target source.target).ty,GeneralNominalRebaseEffectView243.compile (positional env centers) source.mode source.expression⟩

theorem default_exact (env : Syntax) (assignment : Assignment) (centers : List Nat)
 (source : GeneralNominalCenteredHeadMatSchemas.Equation) :
 (defaultEquation env centers source).Holds assignment ↔
 source.Holds (Values.positional (read env assignment) centers) (read env assignment).target := by
 unfold defaultEquation Equation.Holds GeneralNominalCenteredHeadMatSchemas.Equation.Holds
 rw [GeneralNominalRebaseEffectView243.compile_exact]
 rfl

theorem count (outputs : List Nat) (env : Syntax) (schema : Schema) :
 (compile outputs env schema).length = schema.equations.length := by simp [compile]
end Yulang.GeneralNominalRoleEquations251
