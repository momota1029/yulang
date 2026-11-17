import Yulang.GeneralNominalRebaseProjectionView243
import Yulang.GeneralNominalVersionedPlans231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseSchemaView243
open Core.PresenceGeneration (TyTerm CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseOriginView243 (Origin Observes Head Same)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenters (Plan)
open CommonNominalFullCarrier

inductive Requirement where
 | equal (term : TyTerm Nat)
 | interval (lower upper : TyTerm Nat)

def Requirement.Holds (requirement : Requirement) (model : Assignment) (actual : Ty) : Prop :=
 match requirement with
 | .equal term => Equivalent actual (term.eval CommonNominalFullCarrier.model model)
 | .interval lo hi => Subtype (lo.eval CommonNominalFullCarrier.model model) actual ∧ Subtype actual (hi.eval CommonNominalFullCarrier.model model)

def requirement (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
 (mapping : Nat → CompTerm Nat) (name : Nat) (mode : Mode) : Requirement :=
 if name ∈ declaration.outputNames then .equal (mapping (capture.outputs name)).1
 else match mode with
 | .lower => .equal (mapping (capture.inputs name).1).1
 | .upper => .equal (mapping (capture.inputs name).2).1
 | .actual => .interval (mapping (capture.inputs name).1).1 (mapping (capture.inputs name).2).1

theorem requirement_exact (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
 (mapping : Nat → CompTerm Nat) (model : Assignment) (name : Nat) (mode : Mode) (actual : Ty) :
 (requirement declaration capture mapping name mode).Holds model actual ↔
 GeneralNominalMaterialization.VariableHolds declaration capture (read mapping model) name mode actual := by
 unfold requirement GeneralNominalMaterialization.VariableHolds
 split <;> cases mode <;> rfl

inductive Use where
 | same (origin target : Origin)
 | observed (origin : Origin) (requirement : Requirement)

def Use.Holds (use : Use) (model : Assignment) : Prop :=
 match use with
 | .same origin target => Same model origin target
 | .observed origin requirement => (∃ actual, Observes model origin actual) ∧
     ∀ actual, Observes model origin actual → requirement.Holds model actual

def use (plan : Plan roles) (mapping : Nat → CompTerm Nat) (entry : GeneralNominalMaterialization.Use) : Use :=
 if entry.mode = .actual then .same (GeneralNominalRebaseOriginView243.compile mapping entry.origin)
   (.source (mapping (GeneralNominalVersionedFrame231.binder plan entry.name)).1)
 else .observed (GeneralNominalRebaseOriginView243.compile mapping entry.origin)
   (requirement plan.packet.declaration (GeneralNominalVersionedFrame231.capture plan.packet) mapping entry.name entry.mode)

structure Schema where
 tests : List (Origin × GeneralNominalRecursiveInspection.Test)
 uses : List Use
 unknown : Bool

def Schema.Holds (schema : Schema) (model : Assignment) : Prop :=
 (∀ test ∈ schema.tests, Head model test.1 test.2) ∧ ∀ use ∈ schema.uses, use.Holds model

def compile (plan : Plan roles) (mapping : Nat → CompTerm Nat) (schema : GeneralNominalMaterialization.Schema) : Schema :=
 ⟨GeneralNominalRebaseOriginView243.compileTests mapping schema.tests,schema.variables.map (use plan mapping),schema.unknown⟩

theorem use_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (entry : GeneralNominalMaterialization.Use) :
 (use plan mapping entry).Holds model ↔
 (if entry.mode = .actual then GeneralNominalOriginTerms.Same (read mapping model) entry.origin
   (.source (GeneralNominalVersionedFrame231.binder plan entry.name))
 else (∃ actual, GeneralNominalRecursiveInspection.Observes (read mapping model) entry.origin actual) ∧
   ∀ actual, GeneralNominalRecursiveInspection.Observes (read mapping model) entry.origin actual →
   GeneralNominalMaterialization.VariableHolds plan.packet.declaration (GeneralNominalVersionedFrame231.capture plan.packet)
     (read mapping model) entry.name entry.mode actual) := by
 unfold use
 split
 · exact GeneralNominalRebaseOriginView243.same_exact mapping model entry.origin (.source _)
 · simp only [Use.Holds,GeneralNominalRebaseOriginView243.compile_exact,requirement_exact]

theorem compile_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (model : Assignment) (schema : GeneralNominalMaterialization.Schema) :
 (compile plan mapping schema).Holds model ↔ GeneralNominalVersionedPlans231.SchemaHolds plan schema (read mapping model) := by
 unfold Schema.Holds compile GeneralNominalVersionedPlans231.SchemaHolds
 rw [GeneralNominalRebaseOriginView243.tests_exact]
 apply and_congr Iff.rfl
 simp only [List.forall_mem_map,use_exact]

/-- Compilation does not change whether inspection found an unknown shape. -/
theorem unknown_exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (schema : GeneralNominalMaterialization.Schema) :
 (compile plan mapping schema).unknown = schema.unknown := rfl
end Yulang.GeneralNominalRebaseSchemaView243
