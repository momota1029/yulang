import Yulang.GeneralSourceMetadataRoles291

/-! Exact finite manifest of default sources, including unused roles.
An arbitrary existing role environment still needs an attachment theorem. -/
namespace Yulang.GeneralSourceMetadataRoleManifest291
open GeneralSourceMetadataRoles291
open GeneralSourceMetadataDefaults291 (Default Manifest)
open GeneralSourceMetadataFiniteLookup291 (get some_sound some_complete)

def rowDefaults (row : RoleRow) : List Default :=
  row.outputs.filterMap (fun (name,value) => value.map (fun term => ⟨row.role,name,term⟩))

def manifestRows (src : RoleSource) : List Default := src.rows.flatMap rowDefaults

theorem row_exact (row : RoleRow) (d : Default) :
    d ∈ rowDefaults row ↔ d.role = row.role ∧ (d.name,some d.body) ∈ row.outputs := by
  unfold rowDefaults
  constructor
  · intro member
    obtain ⟨⟨name,v⟩,located,shape⟩ := List.mem_filterMap.mp member
    cases v with
    | none => cases shape
    | some rhs =>
      cases Option.some.inj shape
      exact ⟨rfl,located⟩
  · rintro ⟨same,member⟩
    refine List.mem_filterMap.mpr ⟨(d.name,some d.body),member,?_⟩
    cases d
    simp_all

theorem exact_manifest (src : RoleSource) (valid : Valid src) :
    Manifest (roleTable src) (manifestRows src) := by
  intro role name rhs
  constructor
  · intro read
    obtain ⟨row,inSource,inRow⟩ := List.mem_flatMap.mp read
    have pair := (row_exact row _).mp inRow
    have located := lookup_row valid inSource
    have entry := some_complete (valid.2 row inSource) pair.2
    have same : role = row.role := pair.1
    subst role
    unfold roleTable
    rw [located]
    exact entry
  · intro read
    unfold roleTable at read
    cases selected : get role (index src) with
    | none =>
      rw [selected] at read
      cases read
    | some row =>
      rw [selected] at read
      have membership := indexed selected
      exact List.mem_flatMap.mpr ⟨row,membership.1,(row_exact row _).mpr
        ⟨membership.2.symm,some_sound read⟩⟩

theorem attached_manifest (src : RoleSource) (valid : Valid src) (roles : Roles.RoleDecls)
    (correct : roleTable src = roles) : Manifest roles (manifestRows src) :=
  correct ▸ exact_manifest src valid

end Yulang.GeneralSourceMetadataRoleManifest291
