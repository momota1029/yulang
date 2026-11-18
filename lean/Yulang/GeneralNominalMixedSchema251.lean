import Yulang.GeneralNominalRebasePacketView243
/-! Separate historical origin reads from current capture and binder reads. -/
namespace Yulang.GeneralNominalMixedSchema251
open Core.PresenceGeneration (CompTerm TyTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebaseOriginView243 (Origin Observes Same)
open GeneralNominalRebaseSchemaView243 (Use Schema requirement)
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier

def OriginValue (old : Assignment) (origin : GeneralNominalRecursiveInspection.Origin) (target : Ty) : Prop :=
 (∃ value, GeneralNominalRecursiveInspection.Observes old origin value) ∧
 ∀ value, GeneralNominalRecursiveInspection.Observes old origin value → Equivalent value target

theorem same_source (assignment : Assignment) (origin : Origin) (target : TyTerm Nat) :
 Same assignment origin (.source target) ↔
 (∃ value, Observes assignment origin value) ∧
 ∀ value, Observes assignment origin value → Equivalent value (target.eval model assignment) := by
 constructor
 · intro valid
   exact ⟨valid.1,fun value seen => valid.2.2 value _ seen (.source _)⟩
 · rintro ⟨existsValue,valid⟩
   refine ⟨existsValue,⟨_,.source _⟩,?_⟩
   intro first last one two
   cases two
   exact valid first one

def UseHolds (plan : Plan roles) (old current : Assignment) (entry : GeneralNominalMaterialization.Use) : Prop :=
 if entry.mode = .actual then OriginValue old entry.origin (current (GeneralNominalVersionedFrame231.binder plan entry.name)).1
 else (∃ actual, GeneralNominalRecursiveInspection.Observes old entry.origin actual) ∧
 ∀ actual, GeneralNominalRecursiveInspection.Observes old entry.origin actual →
 GeneralNominalMaterialization.VariableHolds plan.packet.declaration (GeneralNominalVersionedFrame231.capture plan.packet)
   current entry.name entry.mode actual

def Holds (plan : Plan roles) (schema : GeneralNominalMaterialization.Schema) (old current : Assignment) : Prop :=
 (∀ test ∈ schema.tests, GeneralNominalOriginTerms.Head old test.1 test.2) ∧
 ∀ entry ∈ schema.variables, UseHolds plan old current entry

def use (plan : Plan roles) (old current : Nat → CompTerm Nat) (entry : GeneralNominalMaterialization.Use) : Use :=
 if entry.mode = .actual then .same (GeneralNominalRebaseOriginView243.compile old entry.origin)
   (.source (current (GeneralNominalVersionedFrame231.binder plan entry.name)).ty)
 else .observed (GeneralNominalRebaseOriginView243.compile old entry.origin)
   (requirement plan.packet.declaration (GeneralNominalVersionedFrame231.capture plan.packet) current entry.name entry.mode)

def compile (plan : Plan roles) (old current : Nat → CompTerm Nat) (schema : GeneralNominalMaterialization.Schema) : Schema :=
 ⟨GeneralNominalRebaseOriginView243.compileTests old schema.tests,schema.variables.map (use plan old current),schema.unknown⟩

theorem use_exact (plan : Plan roles) (old current : Nat → CompTerm Nat) (assignment : Assignment)
 (entry : GeneralNominalMaterialization.Use) :
 (use plan old current entry).Holds assignment ↔ UseHolds plan (read old assignment) (read current assignment) entry := by
 unfold use UseHolds
 split
 · simp only [Use.Holds,same_source,GeneralNominalRebaseOriginView243.compile_exact,OriginValue]
   rfl
 · simp only [Use.Holds,GeneralNominalRebaseOriginView243.compile_exact,GeneralNominalRebaseSchemaView243.requirement_exact]

theorem compile_exact (plan : Plan roles) (old current : Nat → CompTerm Nat) (assignment : Assignment)
 (schema : GeneralNominalMaterialization.Schema) :
 (compile plan old current schema).Holds assignment ↔ Holds plan schema (read old assignment) (read current assignment) := by
 simp only [compile,Schema.Holds,Holds,GeneralNominalRebaseOriginView243.tests_exact,List.forall_mem_map,use_exact]

theorem unknown_exact (plan : Plan roles) (old current : Nat → CompTerm Nat) (schema : GeneralNominalMaterialization.Schema) :
 (compile plan old current schema).unknown = schema.unknown := rfl
end Yulang.GeneralNominalMixedSchema251
