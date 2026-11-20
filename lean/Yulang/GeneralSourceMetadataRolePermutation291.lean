import Yulang.GeneralSourceMetadataPermutation291

/-! An ordered diagnostic list is display data. Its finite role manifest
still names exactly the same defaults when valid role rows are reordered. -/
namespace Yulang.GeneralSourceMetadataRolePermutation291
open GeneralSourceMetadataRoles291 (RoleSource RoleRow Valid roleTable index)
open GeneralSourceMetadataRoleManifest291 (manifestRows exact_manifest)
open GeneralSourceMetadataPermutation291 (get_perm)
open GeneralSourceMetadataDefaults291 (Default)

theorem valid_roles_reorder {s t : RoleSource} (ordered : s.rows.Perm t.rows) (valid : Valid s) :
    Valid t :=
  ⟨(ordered.map RoleRow.role).nodup valid.1,fun r p => valid.2 r (ordered.mem_iff.mpr p)⟩

theorem same_role_table {s t : RoleSource} (ordered : s.rows.Perm t.rows)
    (shared : s.fallbackArity = t.fallbackArity) (valid : Valid s) :
    roleTable s = roleTable t := by
  have p : (index s).Perm (index t) := ordered.map _
  have q : ((index s).map Prod.fst).Nodup := by
    simpa only [index,List.map_map,Function.comp_def] using valid.1
  funext key
  unfold roleTable
  rw [get_perm p q,shared]

theorem same_manifest_membership {s t : RoleSource} (ordered : s.rows.Perm t.rows)
    (shared : s.fallbackArity = t.fallbackArity) (valid : Valid s) (d : Default) :
    d ∈ manifestRows s ↔ d ∈ manifestRows t := by
  rcases d with ⟨role,name,body⟩
  rw [exact_manifest s valid,exact_manifest t (valid_roles_reorder ordered valid),
    same_role_table ordered shared valid]

end Yulang.GeneralSourceMetadataRolePermutation291
