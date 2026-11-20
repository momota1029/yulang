import Yulang.GeneralSourceRoleSyntaxPipeline292
import Yulang.GeneralSourceMetadataBundleFixture291

/-! Compose the auxiliary role adapter with the existing metadata check,
requiring separate attachment for all metadata, roles, and declarations. -/
namespace Yulang.GeneralSourceRoleAttach292
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleSyntaxBoundary292 (Shell)
open GeneralSourceRoleSyntaxPipeline292 (applyShells)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataBundle291 (SourceBundle Certificate Attached inspect ready_exact)
open GeneralSourceMetadataComparison291 (Linked)
open GeneralSourceMetadataRoles291 (RoleSource roleTable Valid)
open GeneralDeclarations (Declaration Registry)
open GeneralNominalCandidates (Context Metadata)
open GeneralNominalCenteredHeadWFSource (Coverage)

structure Input where
  declared : Source
  snapshot : Source
  declarations : List Declaration
  fallbackArity : Nat
  shells : List Shell

def compose (env : Environment) (s : Input) : Option SourceBundle :=
  (applyShells env s.fallbackArity s.shells).map fun roles =>
    ⟨s.declared,s.snapshot,roles,s.declarations⟩

theorem assemble_exact (env : Environment) (s : Input) (out : SourceBundle) :
    compose env s = some out ↔ out.declared = s.declared ∧
      out.snapshot = s.snapshot ∧ out.declarations = s.declarations ∧
      applyShells env s.fallbackArity s.shells = some out.roles := by
  unfold compose
  rcases out with ⟨declared,snapshot,roles,decls⟩
  cases h : applyShells env s.fallbackArity s.shells with
  | none => simp
  | some ts =>
    simp only [Option.map_some,Option.some.injEq,SourceBundle.mk.injEq]
    constructor
    · rintro ⟨a,b,c,d⟩
      exact ⟨a.symm,b.symm,d.symm,c⟩
    · rintro ⟨a,b,c,d⟩
      exact ⟨a.symm,b.symm,d,c.symm⟩

theorem ready_attached {env : Environment} {s : Input} {out : SourceBundle}
    {r : Registry} {ctx : Context} (built : compose env s = some out)
    (tables : Linked s.declared s.snapshot r ctx)
    (roles : roleTable out.roles = r.roles) (declared : s.declarations = r.declarations) :
    (inspect out).ready = true ↔
      GeneralSourceMetadataValidation291.Valid s.declared ∧
      GeneralSourceMetadataValidation291.Valid s.snapshot ∧ Metadata r ctx ∧
      Coverage r ctx.interpretation := by
  obtain ⟨a,b,c,shaped⟩ := (assemble_exact ..).mp built
  have ⟨_,_,_,_,valid⟩ := (GeneralSourceRoleSyntaxPipeline292.pipeline_exact ..).mp shaped
  have attached : Attached out r ctx :=
    ⟨by rw [a,b]; exact tables, roles, c.trans declared⟩
  simp only [ready_exact attached,a,b,valid,true_and]

end Yulang.GeneralSourceRoleAttach292
