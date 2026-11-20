import Yulang.GeneralSourceRoleCstTrackedRow296

/-! The checked table contributes IDs, but must be matched against the
selected original symbolic role, in its exact source order. -/
namespace Yulang.GeneralSourceRoleCstTableEvidence296
open GeneralSourceRoleCstNameCatalog296 (Catalog environment)
open GeneralSourceRoleCstRecoveredCatalog296
  (recoverCatalog recover_catalog_exact inverted_from_lowered recovered_catalog_relowers)
open GeneralSourceRoleCstNamingScope295 (symbolic)
open GeneralSourceRoleCstNamingTrace295 (capture)
open GeneralSourceRoleCstTrackedRow296 (tracked_row_exact)
open GeneralSourceRoleTrack292 (Tracked runTracked)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource check check_exact Valid)
open GeneralSourceMetadataBareRole291 (forgetRow)

def fromTable {S H : Type} (p : Tracked S H) (tab : RoleSource) : Option Catalog :=
  if check tab then
    match symbolic p, tab.rows with
    | some r,[row] => recoverCatalog r.role (forgetRow row)
    | _,_ => none
  else none

theorem from_table_exact {S H : Type} (p : Tracked S H) (tab : RoleSource) (c : Catalog) :
    fromTable p tab = some c ↔ Valid tab ∧ ∃ r row, symbolic p = some r ∧
      tab.rows = [row] ∧ recoverCatalog r.role (forgetRow row) = some c := by
  by_cases h : check tab = true
  · have valid := (check_exact ..).mp h
    cases s : symbolic p with
    | none => simp [fromTable,h,s]
    | some r =>
      cases has : tab.rows with
      | nil => simp [fromTable,h,has,s]
      | cons a as =>
        cases as with
        | nil => simp [fromTable,h,has,s,valid]
        | cons b bs => simp [fromTable,h,has,s]
  · rw [fromTable,ite_eq_right h]
    constructor
    · intro bad; cases bad
    · intro ok; exact False.elim (h ((check_exact ..).mpr ok.1))

theorem actual_table_inverts {S H : Type} (env : S → Environment) (fallback : Nat)
    (p : Tracked S H) (tab : RoleSource) (done : runTracked env fallback [p] = some tab) :
    ∃ r, symbolic p = some r ∧
      fromTable p tab = some (GeneralSourceRoleCstCoalesce296.coalesce (capture (env r.scope) r.role)) := by
  obtain ⟨r,row,ready,one,_,valid,witness⟩ := (tracked_row_exact ..).mp done
  exact ⟨r,ready,(from_table_exact ..).mpr ⟨valid,r,row,ready,one,inverted_from_lowered witness⟩⟩

theorem table_replays {S H : Type} (p : Tracked S H) (tab : RoleSource) (c : Catalog)
    (made : fromTable p tab = some c) :
    ∃ r trace, symbolic p = some r ∧
      GeneralSourceRoleCstCatalogTrace296.produce c r.role = .ok trace ∧
      runTracked (fun _ => environment c) tab.fallbackArity [p] = some tab := by
  obtain ⟨valid,r,row,ready,one,fit⟩ := (from_table_exact ..).mp made
  obtain ⟨trace,_,_,produce⟩ := (recover_catalog_exact ..).mp fit
  exact ⟨r,trace,ready,produce,(tracked_row_exact ..).mpr
    ⟨r,row,ready,one,rfl,valid,recovered_catalog_relowers fit⟩⟩

end Yulang.GeneralSourceRoleCstTableEvidence296
