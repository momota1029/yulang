import Yulang.GeneralSourceRoleCstFixture293

/-! Pair mixed ordinals with an independent parse brand. This does not turn
the brand into a semantic ID or prove that an external serializer is total. -/
namespace Yulang.GeneralSourceRoleCstSnapshot293
open GeneralSourceRoleCstTree293
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleCstPath293 (follow extract_origin)
open GeneralSourceRoleCstProducer293 (extract)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceMetadataExprDomain291 (bind_success)

structure Snapshot (Brand : Type) where
  brand : Brand
  root : Tree

structure Address (Brand : Type) where
  brand : Brand
  path : Path
  deriving DecidableEq, Repr

def atAddress {Brand : Type} [DecidableEq Brand] (s : Snapshot Brand) (a : Address Brand) :
    Option Tree :=
  if a.brand = s.brand then follow a.path s.root else none

theorem address_exact {Brand : Type} [DecidableEq Brand]
    (s : Snapshot Brand) (a : Address Brand) (t : Tree) :
    atAddress s a = some t ↔ a.brand = s.brand ∧ follow a.path s.root = some t := by
  by_cases h : a.brand = s.brand <;> simp [atAddress,h]

def mark {Scope Brand : Type} (brand : Brand) (r : Tracked Scope Path) :
    Tracked Scope (Address Brand) :=
  ⟨r.scope,r.head,⟨brand,r.atRole⟩,r.body.map (fun (p,k) => (⟨brand,p⟩,k))⟩

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

end Yulang.GeneralSourceRoleCstSnapshot293
