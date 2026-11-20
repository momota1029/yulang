import Yulang.GeneralSourceRoleCstRustEntry293

/-! Connect each emitted member to the original supplied JSON wire occurrence
and bound its extent by the supplied token bytes. No Rust producer assumed. -/
namespace Yulang.GeneralSourceRoleCstRustOrigin293
open Lean (Json)
open GeneralSourceRoleCstRustEntry293 (extractText text_exact value_exact)
open GeneralSourceRoleCstJson293 (encode depth)
open GeneralSourceRoleCstWire293 (Wire Transfer spelling transfer_preserves_text)
open GeneralSourceRoleCstWirePaths293 (atWire transfer_path)
open GeneralSourceRoleCstSnapshot293 (Address address_exact)
open GeneralSourceRoleCstRustSnapshot293 (declaration_member_roundtrip)
open GeneralSourceRoleCstSourceExtent293 (lookupExtent extent_exists)
open GeneralSourceRoleCstLossless293 (render_width)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)

theorem text_member_origin {Scope Brand : Type} [DecidableEq Brand]
    (fuel : Nat) (text : String) (scope : Scope) (brand : Brand) (a : Address Brand)
    (payload : Tracked Scope (Address Brand)) (ok : extractText fuel text scope brand a = .ok payload)
    (p : Address Brand × Child) (found : p ∈ payload.body) :
    ∃ json wire root child raw span,
      Json.parse text = .ok json ∧ encode wire = json ∧ depth wire ≤ fuel ∧
      Transfer wire root ∧ p.1.brand = brand ∧
      atWire p.1.path wire = some raw ∧ Transfer raw child ∧
      Classification child p.2 ∧ lookupExtent ⟨brand,root⟩ p.1 = some (child,span) ∧
      span.high = span.low + (spelling raw).utf8ByteSize ∧
      span.high ≤ (spelling wire).utf8ByteSize := by
  obtain ⟨json,parsed,stage⟩ := (text_exact ..).mp ok
  obtain ⟨wire,root,encoded,fits,tree,exported⟩ := (value_exact ..).mp stage
  obtain ⟨child,foundRaw,classifies⟩ :=
    declaration_member_roundtrip scope ⟨brand,root⟩ a payload exported p found
  have arrived := (address_exact ⟨brand,root⟩ p.1 child).mp foundRaw
  obtain ⟨raw,address,linked⟩ := (transfer_path tree p.1.path child).mp arrived.2
  obtain ⟨span,extent,ends,bounded⟩ := extent_exists ⟨brand,root⟩ p.1 child foundRaw
  have e₁ := (render_width child).symm.trans
    (congrArg String.utf8ByteSize (transfer_preserves_text linked))
  have e₂ := (render_width root).symm.trans
    (congrArg String.utf8ByteSize (transfer_preserves_text tree))
  exact ⟨json,wire,root,child,raw,span,parsed,encoded,fits,tree,arrived.1,address,linked,
    classifies,extent,e₁ ▸ ends,e₂ ▸ bounded⟩

end Yulang.GeneralSourceRoleCstRustOrigin293
