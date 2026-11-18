import Yulang.GeneralNominalRoleEquations251
namespace Yulang.GeneralNominalRoleRequests251
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (translate value)
open GeneralNominalRebaseEffectView243 (Equation)
open CommonNominalFullCarrier

structure Request where
 pattern : GeneralDeclarationPatterns.Pattern
 target : TyTerm Nat
 mode : Mode

structure Compiled where
 equations : List Equation
 unknown : Bool

def materialize (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (env : Syntax) (request : Request) : Compiled :=
 match translate catalogue interpretation request.pattern with
 | none => ⟨[],true⟩
 | some expression => ⟨[⟨request.target,GeneralNominalRebaseEffectView243.compile (variables outputs env) request.mode expression⟩],false⟩

def Holds (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (values : Values) (assignment : Assignment) (request : Request) : Prop :=
 ∀ expression, translate catalogue interpretation request.pattern = some expression →
 Equivalent (request.target.eval model assignment) (value (values.variables outputs) request.mode expression)

theorem materialize_exact (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (env : Syntax) (assignment : Assignment) (request : Request) :
 GeneralNominalRebasePacketView243.AllEquations (materialize catalogue interpretation outputs env request).equations assignment ↔
 Holds catalogue interpretation outputs (read env assignment) assignment request := by
 cases translated : translate catalogue interpretation request.pattern with
 | none => simp [materialize,translated,GeneralNominalRebasePacketView243.AllEquations,Holds]
 | some expression =>
   simp only [materialize,translated,GeneralNominalRebasePacketView243.AllEquations,List.mem_singleton,forall_eq,Holds,Option.some.injEq,forall_eq']
   unfold Equation.Holds
   rw [GeneralNominalRebaseEffectView243.compile_exact]
   have same : (fun mode name => (variables outputs env mode name).eval model assignment) =
     (read env assignment).variables outputs := funext fun mode => funext fun name => variables_exact outputs env assignment mode name
   rw [same]

def compile (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (env : Syntax) : List Request → Compiled
 | [] => ⟨[],false⟩
 | first :: rest =>
   let head := materialize catalogue interpretation outputs env first
   let tail := compile catalogue interpretation outputs env rest
   ⟨head.equations ++ tail.equations,head.unknown || tail.unknown⟩

theorem compile_exact (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (env : Syntax) (assignment : Assignment) (requests : List Request) :
 GeneralNominalRebasePacketView243.AllEquations (compile catalogue interpretation outputs env requests).equations assignment ↔
 ∀ request ∈ requests, Holds catalogue interpretation outputs (read env assignment) assignment request := by
 induction requests with
 | nil => simp [compile,GeneralNominalRebasePacketView243.AllEquations]
 | cons first rest ih =>
   simp only [compile,GeneralNominalRebasePacketView243.AllEquations,List.forall_mem_append,List.forall_mem_cons]
   exact and_congr (materialize_exact catalogue interpretation outputs env assignment first) ih

theorem materialize_known (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (env : Syntax) (request : Request) :
 (materialize catalogue interpretation outputs env request).unknown = false ↔
 ∃ expression, translate catalogue interpretation request.pattern = some expression := by
 cases translated : translate catalogue interpretation request.pattern <;> simp [materialize,translated]

theorem known_iff (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (env : Syntax) (requests : List Request) :
 (compile catalogue interpretation outputs env requests).unknown = false ↔
 ∀ request ∈ requests, ∃ expression, translate catalogue interpretation request.pattern = some expression := by
 induction requests with
 | nil => simp [compile]
 | cons first rest ih =>
   simp only [compile,Bool.or_eq_false_iff,List.forall_mem_cons]
   exact and_congr (materialize_known catalogue interpretation outputs env first) ih
end Yulang.GeneralNominalRoleRequests251
