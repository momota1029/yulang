import Yulang.GeneralNominalRoleRequests251
namespace Yulang.GeneralNominalRoleChild251
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalCenters (Plan)
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalRebaseLiveView243 (Argument Site Output)
open CommonNominalFullCarrier

def pattern (clause : Clause) (valid : clause.Signature roles) (index : Fin (roles clause.role).arity) : Pattern :=
 clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)

def allocation (plan : Plan roles) (clause : Clause) :=
 (GeneralNominalVersionedFrame231.frame plan.packet).allocation plan.packet.declaration.id clause

def center (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles)
 (index : Fin (roles clause.role).arity) : TyTerm Nat :=
 match normalize (pattern clause valid index) with
 | .var name => env.binder name
 | _ => (env.target (GeneralNominalVersionedFrame231.emittedCenter plan clause.id index.val (pattern clause valid index))).ty

def argument (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles)
 (index : Fin (roles clause.role).arity) : GeneralNominalRebaseLiveView243.Argument :=
 match normalize (pattern clause valid index) with
 | .var name => ⟨(env.capture name).lower,(env.capture name).upper,env.binder name⟩
 | _ => ⟨(env.target ((allocation plan clause).arguments index).1).ty,
   (env.target ((allocation plan clause).arguments index).2).ty,center plan env clause valid index⟩

def ArgumentHolds (plan : Plan roles) (values : Values) (clause : Clause) (valid : clause.Signature roles)
 (index : Fin (roles clause.role).arity) : Prop :=
 match normalize (pattern clause valid index) with
 | .var name => Subtype (values.lower name) (values.binder name) ∧ Subtype (values.binder name) (values.upper name)
 | _ =>
   Subtype (values.target ((allocation plan clause).arguments index).1).1
     (values.target (GeneralNominalVersionedFrame231.emittedCenter plan clause.id index.val (pattern clause valid index))).1 ∧
   Subtype (values.target (GeneralNominalVersionedFrame231.emittedCenter plan clause.id index.val (pattern clause valid index))).1
     (values.target ((allocation plan clause).arguments index).2).1

def outputTarget (plan : Plan roles) (env : Syntax) (clause : Clause) (equation : GeneralDeclarations.Equation) : TyTerm Nat :=
 match normalize equation.rhs with
 | .var name => if name ∈ plan.packet.declaration.outputNames then env.binder name
   else (env.target ((allocation plan clause).outputs equation.id)).ty
 | _ => (env.target ((allocation plan clause).outputs equation.id)).ty

def site (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) : Site :=
 ⟨(GeneralNominalVersionedFrame231.clauseChild plan.packet clause valid).identity,clause.role,
 List.ofFn (argument plan env clause valid),clause.outputs.map fun equation => ⟨equation.name,outputTarget plan env clause equation⟩⟩

theorem argument_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) (clause : Clause)
 (valid : clause.Signature roles) (index : Fin (roles clause.role).arity) :
 (argument plan env clause valid index).Holds assignment ↔ ArgumentHolds plan (read env assignment) clause valid index := by
 unfold argument ArgumentHolds center
 cases normalize (pattern clause valid index) <;> rfl

theorem site_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) (clause : Clause)
 (valid : clause.Signature roles) :
 (site plan env clause valid).Holds assignment ↔ ∀ index, ArgumentHolds plan (read env assignment) clause valid index := by
 unfold site Site.Holds
 constructor
 · intro held index
   exact (argument_exact plan env assignment clause valid index).mp (held _ (List.mem_ofFn.mpr ⟨index,rfl⟩))
 · intro held item member
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
   exact (argument_exact plan env assignment clause valid index).mpr (held index)

def requests (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) : List GeneralNominalRoleRequests251.Request :=
 List.ofFn fun index : Fin (roles clause.role).arity => ⟨pattern clause valid index,center plan env clause valid index,.actual⟩

def compile (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) : GeneralNominalRebasePacketView243.Child :=
 ⟨site plan env clause valid,(GeneralNominalRoleRequests251.compile plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration.outputNames env (requests plan env clause valid)).equations⟩

def Holds (plan : Plan roles) (env : Syntax) (values : Values) (assignment : Assignment) (clause : Clause)
 (valid : clause.Signature roles) : Prop :=
 (∀ index, ArgumentHolds plan values clause valid index) ∧
 ∀ request ∈ requests plan env clause valid,
 GeneralNominalRoleRequests251.Holds plan.packet.registry.constructors plan.packet.context.interpretation
   plan.packet.declaration.outputNames values assignment request

theorem compile_exact (plan : Plan roles) (env : Syntax) (assignment : Assignment) (clause : Clause) (valid : clause.Signature roles) :
 (compile plan env clause valid).Holds assignment ↔ Holds plan env (read env assignment) assignment clause valid := by
 unfold compile GeneralNominalRebasePacketView243.Child.Holds Holds
 rw [site_exact,GeneralNominalRoleRequests251.compile_exact]

theorem request_count (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) :
 (requests plan env clause valid).length = (roles clause.role).arity := by simp [requests]

theorem identity_preserved (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) :
 (site plan env clause valid).identity = (plan.childSite clause valid).occurrence.identity := GeneralNominalVersionedFrame231.childSite_identity_eq plan clause valid

theorem output_count (plan : Plan roles) (env : Syntax) (clause : Clause) (valid : clause.Signature roles) :
 (site plan env clause valid).outputs.length = clause.outputs.length := by simp [site]
end Yulang.GeneralNominalRoleChild251
