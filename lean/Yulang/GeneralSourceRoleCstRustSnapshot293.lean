import Yulang.GeneralSourceRoleCstRustRole293

/-! Snapshot entry for the real Rust TypeApplyArgument wrapper topology.
All member locations are from the original root. -/
namespace Yulang.GeneralSourceRoleCstRustSnapshot293
open GeneralSourceRoleCstSnapshot293 (Address Snapshot atAddress address_exact mark)
open GeneralSourceRoleCstRustRole293 (extract extract_origin)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceMetadataExprDomain291 (bind_success)

def exportAt {Scope Brand : Type} [DecidableEq Brand] (scope : Scope) (s : Snapshot Brand)
    (a : Address Brand) : Option (Tracked Scope (Address Brand)) :=
  (atAddress s a).bind fun t => (extract scope a.path t).map (mark s.brand)

theorem export_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand)) :
    exportAt scope s a = some out ↔
      a.brand = s.brand ∧
      ∃ t raw, follow a.path s.root = some t ∧
        extract scope a.path t = some raw ∧ mark s.brand raw = out := by
  constructor
  · intro ok
    obtain ⟨t,picked,found⟩ := bind_success ok
    have link := (address_exact ..).mp picked
    cases raw : extract scope a.path t with
    | none => simp [raw] at found
    | some tracked =>
      have eq : mark s.brand tracked = out := by simpa [raw] using found
      exact ⟨link.1,t,tracked,link.2,raw,eq⟩
  · rintro ⟨brand,t,tracked,picked,found,rfl⟩
    simp [exportAt,(address_exact ..).mpr ⟨brand,picked⟩,found]

theorem declaration_member_roundtrip {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (out : Tracked Scope (Address Brand))
    (ok : exportAt scope s a = some out) (p : Address Brand × Child) (member : p ∈ out.body) :
    ∃ t, atAddress s p.1 = some t ∧ Classification t p.2 := by
  obtain ⟨_,root,raw,selected,fromRoot,rfl⟩ := (export_exact ..).mp ok
  obtain ⟨pair,inRaw,e⟩ := List.mem_map.mp member
  rcases pair with ⟨path,c⟩
  change (⟨s.brand,path⟩,c) = p at e
  subst p
  obtain ⟨t,same,valid⟩ := extract_origin selected fromRoot _ inRaw
  exact ⟨t,(address_exact ..).mpr ⟨rfl,same⟩,valid⟩

theorem foreign_export_none {Scope Brand : Type} [DecidableEq Brand]
    (scope : Scope) (s : Snapshot Brand) (a : Address Brand) (foreign : a.brand ≠ s.brand) :
    exportAt scope s a = none := by simp [exportAt,atAddress,foreign]

end Yulang.GeneralSourceRoleCstRustSnapshot293
