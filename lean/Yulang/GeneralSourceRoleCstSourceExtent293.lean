import Yulang.GeneralSourceRoleCstRecovery293
import Yulang.GeneralSourceRoleCstConsumer293
import Yulang.GeneralSourceRoleCstLossless293

/-! A scoped associated declaration can be located in the *same supplied*
snapshot. Byte bounds do not authenticate an untrusted Rust export. -/
namespace Yulang.GeneralSourceRoleCstSourceExtent293
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstSpan293 (Extent locate locate_tree locate_bounds width)
open GeneralSourceRoleCstSnapshot293 (Snapshot Address atAddress exportAt)
open GeneralSourceRoleTrack292 (Tracked runTracked)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceRoleSyntaxBoundary292 (Shape)
open GeneralSourceRoleCstTypeRules293 (IsType type_exact)

def lookupExtent {Brand : Type} [DecidableEq Brand] (s : Snapshot Brand) (address : Address Brand) :
    Option (Tree × Extent) :=
  if address.brand = s.brand then locate address.path s.root 0 else none

theorem extent_projection {Brand : Type} [DecidableEq Brand] (s : Snapshot Brand)
    (address : Address Brand) : (lookupExtent s address).map Prod.fst = atAddress s address := by
  by_cases h : address.brand = s.brand
  · simp [lookupExtent,atAddress,h,locate_tree]
  · simp [lookupExtent,atAddress,h]

theorem extent_exists {Brand : Type} [DecidableEq Brand] (s : Snapshot Brand)
    (address : Address Brand) (t : Tree) (found : atAddress s address = some t) :
    ∃ ext, lookupExtent s address = some (t,ext) ∧
      ext.high = ext.low + width t ∧ ext.high ≤ width s.root := by
  rw [← extent_projection] at found
  cases read : lookupExtent s address with
  | none => simp [read] at found
  | some pair =>
    obtain ⟨raw,ext⟩ := pair
    simp only [read,Option.map_some,Option.some.injEq] at found
    subst raw
    have owner := (GeneralSourceRoleCstSnapshot293.address_exact s address t).mp
      ((extent_projection s address).symm ▸ by simp [read])
    have located : locate address.path s.root 0 = some (t, ext) := by
      simpa [lookupExtent,owner.1] using read
    have bounds := locate_bounds located
    exact ⟨ext,rfl,bounds.2.1,by simpa using bounds.2.2⟩

theorem attached_associated_extent {Scope Brand : Type} [DecidableEq Brand]
    (s : Snapshot Brand) (a : Address Brand) (scope : Scope)
    (payload : Tracked Scope (Address Brand)) (produced : exportAt scope s a = some payload)
    (env : Scope → Environment) (fallback : Nat) (table : RoleSource)
    (attached : runTracked env fallback [payload] = some table)
    (roleID nameID : Nat) (value : Option Roles.Term)
    (read : (roleTable table roleID).assoc nameID = some value) :
    ∃ site t span sh, (site,.typeDecl sh) ∈ payload.body ∧
      lookupExtent s site = some (t,span) ∧ IsType t sh ∧
      span.high = span.low + width t ∧ span.high ≤ width s.root := by
  obtain ⟨site,t,sh,stays,node,classify⟩ :=
    GeneralSourceRoleCstConsumer293.assoc_locates_type s a scope payload produced env fallback
      table attached roleID nameID value read
  obtain ⟨span,extent,size,bounded⟩ := extent_exists s site t node
  cases classify with
  | associated cs sh correct =>
    exact ⟨site,_,span,sh,stays,extent,(type_exact ..).mp correct,size,bounded⟩

end Yulang.GeneralSourceRoleCstSourceExtent293
