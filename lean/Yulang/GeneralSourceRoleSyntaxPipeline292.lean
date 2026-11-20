import Yulang.GeneralSourceRoleSyntaxBoundary292
import Yulang.GeneralSourceRoleFixture292

/-! Composition from the explicitly modeled syntax boundary, not compilation
from source bytes. Requires a parser-owned producer of these shells. -/
namespace Yulang.GeneralSourceRoleSyntaxPipeline292
open GeneralSourceRoleSpelling292 GeneralSourceRoleExport292 GeneralSourceRoleSyntaxBoundary292
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceRoleManifest292 (Origin)
open GeneralSourceMetadataExprDomain291 (bind_success)

def ShellWitness (s : Shell) (r : Role) : Prop :=
  s.name = r.spelling ∧ s.parameters = r.binders ∧
  Aligned (Admitted .roleBodyDirect) s.directTypeChildren r.outputs

def applyShells (env : Environment) (fallback : Nat) (shells : List Shell) : Option RoleSource :=
  (collect projectRole shells).bind (lower env fallback)

theorem pipeline_exact (env : Environment) (fallback : Nat) (shells : List Shell) (out : RoleSource) :
    applyShells env fallback shells = some out ↔ ∃ symbolic,
      Aligned ShellWitness shells symbolic ∧
      out.fallbackArity = fallback ∧
      Aligned (RowWitness env) symbolic (out.rows.map GeneralSourceMetadataBareRole291.forgetRow) ∧
      GeneralSourceMetadataRoles291.Valid out := by
  constructor
  · intro h
    obtain ⟨roles, projected, result⟩ := bind_success h
    exact ⟨roles, (collect_exact _ ShellWitness projectRole_exact _ _).mp projected,
      (lower_exact ..).mp result⟩
  · rintro ⟨roles, projected, result⟩
    unfold applyShells
    rw [(collect_exact _ ShellWitness projectRole_exact _ _).mpr projected]
    exact (lower_exact ..).mpr result

theorem default_from_shells (env : Environment) (fallback : Nat) (shells : List Shell)
    (out : RoleSource) (h : applyShells env fallback shells = some out)
    (rid name : Nat) (term : Roles.Term) :
    (roleTable out rid).assoc name = some (some term) ↔
      ∃ s ∈ shells, env.role s.name = some rid ∧
        ∃ el ∈ s.directTypeChildren, ∃ o, Admitted .roleBodyDirect el o ∧
          env.output rid o.spelling = some name ∧ ResolvedBody env s.parameters o.body (some term) := by
  obtain ⟨symbolic, shape, lowered⟩ := (pipeline_exact ..).mp h
  have executable := (lower_exact env fallback symbolic out).mpr lowered
  rw [GeneralSourceRoleManifest292.runtime_default_exact executable]
  constructor
  · rintro ⟨r,inInput,roleID,o,inRole,outID,bodyOK⟩
    obtain ⟨s,inShell,owner⟩ := GeneralSourceRoleManifest292.aligned_right shape inInput
    obtain ⟨el,inBody,syntaxOK⟩ := GeneralSourceRoleManifest292.aligned_right owner.2.2 inRole
    exact ⟨s,inShell,owner.1.symm ▸ roleID,el,inBody,o,syntaxOK,outID,owner.2.1.symm ▸ bodyOK⟩
  · rintro ⟨s,inShell,roleID,el,inBody,o,syntaxOK,outID,bodyOK⟩
    obtain ⟨r,inInput,owner⟩ := GeneralSourceRoleManifest292.aligned_left shape inShell
    obtain ⟨projected,inRole,resolved⟩ := GeneralSourceRoleManifest292.aligned_left owner.2.2 inBody
    have same : o = projected := Option.some.inj
      (((projection_exact ..).mpr syntaxOK).symm.trans ((projection_exact ..).mpr resolved))
    subst projected
    exact ⟨r,inInput,owner.1 ▸ roleID,o,inRole,outID,owner.2.1 ▸ bodyOK⟩

end Yulang.GeneralSourceRoleSyntaxPipeline292
