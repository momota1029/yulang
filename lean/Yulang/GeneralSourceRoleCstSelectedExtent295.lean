import Yulang.GeneralSourceRoleCstHeadOrigin295

/-! Source locations are half-open UTF-8 byte spans in the same supplied wire.
They are checked relative to the selected declaration, not the file as a whole. -/
namespace Yulang.GeneralSourceRoleCstSelectedExtent295
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstSpan293 (Extent locate width prefixWidth locate_bounds)
open GeneralSourceRoleCstMarkSpans294 (reach_has_extent)
open GeneralSourceRoleCstWire293 (Wire Transfer spelling transfer_preserves_text)
open GeneralSourceRoleCstWirePaths293 (atWire transfer_path)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleCstSealOrigin295 (kept_export)
open GeneralSourceRoleCstSelectedMembers295 (exported_member_prefix)
open GeneralSourceRoleCstSnapshot293 (Address address_exact)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstLossless293 (render_width)

theorem locate_append (p q : Path) (root : Tree) (start : Nat) :
    locate (p ++ q) root start =
      (locate p root start).bind (fun hit => locate q hit.1 hit.2.low) := by
  induction p generalizing root start with
  | nil => rfl
  | cons i tail ih =>
    cases root with
    | token => rfl
    | node tag cs =>
      cases c : cs[i]? with
      | none => simp [locate,c]
      | some child => simpa [locate,c] using ih child (start+prefixWidth i cs)

theorem subextent {root parent child : Tree} {start : Nat} {p q : Path}
    {outer inner : Extent}
    (base : locate p root start = some (parent,outer))
    (nested : locate (p ++ q) root start = some (child,inner)) :
    outer.low ≤ inner.low ∧ inner.high ≤ outer.high := by
  rw [locate_append,base,Option.bind_some] at nested
  have parentBound := (locate_bounds base).2.1
  have h : outer.low ≤ inner.low ∧ inner.high = inner.low + width child ∧
      inner.high ≤ outer.low + width parent := locate_bounds nested
  exact ⟨h.1,by omega⟩

theorem selected_member_contained {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (payload : Tracked S (Address B))
    (accepted : select policy scope w brand a packet = some payload)
    (item : Address B × Child) (member : item ∈ payload.body) :
    ∃ root selected t raw outer inside, Transfer w root ∧
      locate a.path root 0 = some (selected,outer) ∧
      locate item.1.path root 0 = some (t,inside) ∧
      atWire item.1.path w = some raw ∧ Transfer raw t ∧ Classification t item.2 ∧
      outer.low ≤ inside.low ∧ inside.high ≤ outer.high ∧
      inside.high = inside.low + (spelling raw).utf8ByteSize := by
  obtain ⟨root,mapping,exported⟩ := kept_export policy scope w brand a packet payload accepted
  obtain ⟨_,selectTree,_,rawSelect,_,_⟩ :=
    (GeneralSourceRoleCstRustSnapshot293.export_exact ..).mp exported
  obtain ⟨outSpan,outLocation⟩ := reach_has_extent rawSelect
  obtain ⟨node,loc,cl⟩ := GeneralSourceRoleCstRustSnapshot293.declaration_member_roundtrip
    scope ⟨brand,root⟩ a payload exported item member
  have locRaw := ((address_exact ..).mp loc).2
  obtain ⟨inSpan,inLocation⟩ := reach_has_extent locRaw
  obtain ⟨raw,found,connection⟩ := (transfer_path mapping _ _).mp locRaw
  obtain ⟨_,b,st,i,suffix⟩ := exported_member_prefix scope ⟨brand,root⟩ a payload exported item member
  have bounds := subextent outLocation (suffix ▸ inLocation)
  have size := (render_width node).symm.trans
    (congrArg String.utf8ByteSize (transfer_preserves_text connection))
  exact ⟨root,selectTree,node,raw,outSpan,inSpan,mapping,outLocation,inLocation,found,connection,cl,
    bounds.1,bounds.2,size ▸ (locate_bounds inLocation).2.1⟩

end Yulang.GeneralSourceRoleCstSelectedExtent295
