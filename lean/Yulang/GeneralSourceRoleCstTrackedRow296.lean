import Yulang.GeneralSourceRoleCstRecoveredControl296

/-! Relate the actually selected old tracked exporter to its unique bare row,
including the table validator. This does not assign a role ID from the path. -/
namespace Yulang.GeneralSourceRoleCstTrackedRow296
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleTrack292 (Tracked runTracked)
open GeneralSourceRoleCstNamingScope295 (symbolic tracked_symbolic)
open GeneralSourceRoleScopedExport292 (ScopedRole lower lower_exact)
open GeneralSourceRoleCstSelectedRow295 (aligned_singleton map_singleton)
open GeneralSourceMetadataRoles291 (RoleSource RoleRow Valid)
open GeneralSourceMetadataBareRole291 (forgetRow)
open GeneralSourceRoleExport292 (resolveRole role_exact)

theorem tracked_row_exact {S H : Type} (env : S → Environment) (f : Nat)
    (p : Tracked S H) (tab : RoleSource) :
    runTracked env f [p] = some tab ↔ ∃ r row, symbolic p = some r ∧
      tab.rows = [row] ∧ tab.fallbackArity = f ∧ Valid tab ∧
      resolveRole (env r.scope) r.role = some (forgetRow row) := by
  constructor
  · intro ok
    rw [tracked_symbolic] at ok
    cases hs : symbolic p with
    | none => simp [hs] at ok
    | some r =>
      have made : lower env f [r] = some tab := by simpa [hs] using ok
      obtain ⟨fb,aligned,valid⟩ := (lower_exact ..).mp made
      obtain ⟨br,one,model⟩ := aligned_singleton aligned
      obtain ⟨row,just,same⟩ := map_singleton one
      refine ⟨r,row,rfl,just,fb,valid,(role_exact ..).mpr ?_⟩
      rw [same]
      exact model
  · rintro ⟨r,row,hs,just,fb,valid,decided⟩
    rw [tracked_symbolic,hs,Option.bind_some]
    apply (lower_exact ..).mpr
    refine ⟨fb,?_,valid⟩
    rw [just,List.map_cons,List.map_nil]
    exact .cons ((role_exact ..).mp decided) .nil

end Yulang.GeneralSourceRoleCstTrackedRow296
