import Yulang.GeneralNominalRoleEnvironment251
namespace Yulang.GeneralNominalRoleSchema251
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalRebaseSchemaView243 (Use Schema)
open GeneralNominalMixedSchema251 (OriginValue same_source)
open CommonNominalFullCarrier

def UseHolds (outputs : List Nat) (values : Values) (entry : GeneralNominalMaterialization.Use) : Prop :=
 if entry.mode = .actual then OriginValue values.old entry.origin (values.binder entry.name)
 else (∃ actual, GeneralNominalRecursiveInspection.Observes values.old entry.origin actual) ∧
 ∀ actual, GeneralNominalRecursiveInspection.Observes values.old entry.origin actual →
 Requirement outputs values entry.name entry.mode actual

def Holds (outputs : List Nat) (schema : GeneralNominalMaterialization.Schema) (values : Values) : Prop :=
 (∀ test ∈ schema.tests, GeneralNominalOriginTerms.Head values.old test.1 test.2) ∧
 ∀ entry ∈ schema.variables, UseHolds outputs values entry

def use (outputs : List Nat) (env : Syntax) (entry : GeneralNominalMaterialization.Use) : Use :=
 if entry.mode = .actual then .same (GeneralNominalRebaseOriginView243.compile env.old entry.origin) (.source (env.binder entry.name))
 else .observed (GeneralNominalRebaseOriginView243.compile env.old entry.origin) (requirement outputs env entry.name entry.mode)

def compile (outputs : List Nat) (env : Syntax) (schema : GeneralNominalMaterialization.Schema) : Schema :=
 ⟨GeneralNominalRebaseOriginView243.compileTests env.old schema.tests,schema.variables.map (use outputs env),schema.unknown⟩

theorem use_exact (outputs : List Nat) (env : Syntax) (assignment : Assignment) (entry : GeneralNominalMaterialization.Use) :
 (use outputs env entry).Holds assignment ↔ UseHolds outputs (read env assignment) entry := by
 unfold use UseHolds
 split
 · simp only [Use.Holds,same_source,GeneralNominalRebaseOriginView243.compile_exact,OriginValue]
   rfl
 · simp only [Use.Holds,GeneralNominalRebaseOriginView243.compile_exact,requirement_exact]
   rfl

theorem compile_exact (outputs : List Nat) (env : Syntax) (assignment : Assignment) (schema : GeneralNominalMaterialization.Schema) :
 (compile outputs env schema).Holds assignment ↔ Holds outputs schema (read env assignment) := by
 simp only [compile,Schema.Holds,Holds,GeneralNominalRebaseOriginView243.tests_exact,List.forall_mem_map,use_exact]
 rfl

theorem origin_value_related (old : Assignment) (origin : GeneralNominalRecursiveInspection.Origin)
 (same : Equivalent first last) : OriginValue old origin first ↔ OriginValue old origin last := by
 unfold OriginValue
 apply and_congr Iff.rfl
 apply forall_congr'; intro value
 apply forall_congr'; intro _seen
 exact GeneralNominalRawCongruence238.equiv_iff ⟨subtype_refl _,subtype_refl _⟩ same

theorem use_related (same : Related first last) (outputs : List Nat) (entry : GeneralNominalMaterialization.Use) :
 UseHolds outputs first entry ↔ UseHolds outputs last entry := by
 unfold UseHolds
 split
 · rw [same.old]
   exact origin_value_related _ _ (same.binder entry.name)
 · rw [same.old]
   apply and_congr Iff.rfl
   apply forall_congr'; intro actual
   apply forall_congr'; intro _seen
   exact requirement_related same outputs entry.name entry.mode actual

theorem holds_related (same : Related first last) (outputs : List Nat) (schema : GeneralNominalMaterialization.Schema) :
 Holds outputs schema first ↔ Holds outputs schema last := by
 unfold Holds
 apply and_congr
 · rw [same.old]
 · exact forall_congr' fun entry => forall_congr' fun _ => use_related same outputs entry

theorem unknown_exact (outputs : List Nat) (env : Syntax) (schema : GeneralNominalMaterialization.Schema) :
 (compile outputs env schema).unknown = schema.unknown := rfl
end Yulang.GeneralNominalRoleSchema251
