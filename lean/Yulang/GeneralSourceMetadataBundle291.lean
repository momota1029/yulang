import Yulang.GeneralSourceMetadataComparison291

/-! Complete executable evidence for a fixed resolved source fragment.
Metadata, source validation and materialization are independent fields. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataBundle291
open GeneralSourceMetadataRows291 (Source constructors interpretation)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceMetadataComparison291 (Linked Result compare exact_linked_metadata)
open GeneralSourceMetadataDiagnostics291 (Failure diagnostics no_diagnostics_iff)
open GeneralSourceMetadataRoleManifest291 (manifestRows exact_manifest)
open GeneralDeclarations (Declaration Registry)
open GeneralNominalCandidates (Context Metadata)
open GeneralNominalCenteredHeadWFSource (Coverage)

structure SourceBundle where
  declared : Source
  snapshot : Source
  roles : RoleSource
  declarations : List Declaration

def registry (s : SourceBundle) : Registry :=
  ⟨constructors s.declared,roleTable s.roles,s.declarations⟩

structure Certificate where
  declarationsValid : Bool
  snapshotValid : Bool
  roleKeysValid : Bool
  tables : Result
  unsupported : List Failure
  deriving DecidableEq, Repr

def inspect (s : SourceBundle) : Certificate :=
  ⟨GeneralSourceMetadataValidation291.check s.declared,
   GeneralSourceMetadataValidation291.check s.snapshot,
   GeneralSourceMetadataRoles291.check s.roles,
   compare s.declared s.snapshot [],
   diagnostics (registry s) (interpretation s.snapshot) (manifestRows s.roles)⟩

def Certificate.ready (q : Certificate) : Bool :=
  q.declarationsValid && q.snapshotValid && q.roleKeysValid &&
    decide (q.tables = .compared .good) && q.unsupported.isEmpty

structure Attached (s : SourceBundle) (r : Registry) (ctx : Context) : Prop where
  tables : Linked s.declared s.snapshot r ctx
  roles : roleTable s.roles = r.roles
  declarations : s.declarations = r.declarations

theorem actual_registry {s : SourceBundle} {r : Registry} {ctx : Context}
    (attached : Attached s r ctx) : registry s = r := by
  unfold registry
  rw [← attached.tables.declaredCorrect,attached.roles,attached.declarations]

theorem ready_exact {s : SourceBundle} {r : Registry} {ctx : Context} (attached : Attached s r ctx) :
    (inspect s).ready = true ↔
      GeneralSourceMetadataValidation291.Valid s.declared ∧
      GeneralSourceMetadataValidation291.Valid s.snapshot ∧
      GeneralSourceMetadataRoles291.Valid s.roles ∧ Metadata r ctx ∧ Coverage r ctx.interpretation := by
  simp only [Certificate.ready,inspect,Bool.and_eq_true,decide_eq_true_eq,List.isEmpty_iff,
    GeneralSourceMetadataValidation291.check_exact,GeneralSourceMetadataRoles291.check_exact,and_assoc]
  rw [exact_linked_metadata attached.tables,actual_registry attached,← attached.tables.interpretationCorrect]
  constructor
  · rintro ⟨d,t,roles,md,empty⟩
    have complete := GeneralSourceMetadataRoleManifest291.attached_manifest _ roles _ attached.roles
    exact ⟨d,t,roles,md,(no_diagnostics_iff _ _ _ complete).mp empty⟩
  · rintro ⟨d,t,roles,md,coverage⟩
    have complete := GeneralSourceMetadataRoleManifest291.attached_manifest _ roles _ attached.roles
    exact ⟨d,t,roles,md,(no_diagnostics_iff _ _ _ complete).mpr coverage⟩

end Yulang.GeneralSourceMetadataBundle291
