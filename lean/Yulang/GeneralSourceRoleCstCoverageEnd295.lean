import Yulang.GeneralSourceRoleCstSelectedCoverage295

/-! In the supported selected fragment, no typed member is silently dropped
between portable text and the old role table when the handoff succeeds. -/
namespace Yulang.GeneralSourceRoleCstCoverageEnd295
open Lean (Json)
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstWirePaths293 (atWire)
open GeneralSourceRoleCstJson293 (encode depth)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedJson295 (fromText text_exact)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary checked_exact)
open GeneralSourceRoleCstSelectedCoverage295 (selected_type_contributes)
open GeneralSourceRoleCstSelectedMembers295 (selected_member_is_exact_original)
open GeneralSourceRoleTrack292 (Tracked OriginAt)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleCstRawType295 (type_evidence_original_node)

theorem text_has_every_selected_type {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (text : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat)
    (tab : RoleSource) (ok : fromText fuel text policy scope brand a packet env fallback = .ok tab) :
    ∃ (j : Json) (w : Wire) (p : Tracked S (Address B)),
      Json.parse text = .ok j ∧ encode w = j ∧ depth w ≤ fuel ∧ p.atRole = a ∧
      GeneralSourceRoleCstSelectedSeal295.select policy scope w brand a packet.selected.selected = some p ∧
      ∀ site shape, (site,Child.typeDecl shape) ∈ p.body →
        ∃ role name value children b stmt leaf,
          OriginAt env [p] role name value a site ∧
          (roleTable tab role).assoc name = some value ∧
          site.path = a.path ++ [b,stmt,leaf] ∧ atWire site.path w = some (.node "TypeDeclaration" children) := by
  obtain ⟨j,w,parsed,encoded,allowed,bound⟩ := (text_exact ..).mp ok
  obtain ⟨_,built⟩ := (checked_exact ..).mp bound
  obtain ⟨p,site,got,all⟩ := selected_type_contributes policy scope w brand a packet.selected env fallback tab built
  refine ⟨j,w,p,parsed,encoded,allowed,site,got,?_⟩
  intro member shape here
  obtain ⟨role,name,value,witness,read⟩ := all member shape here
  obtain ⟨_,⟨b,st,leaf,place⟩,t,raw,atRaw,transfer,kind⟩ :=
    selected_member_is_exact_original policy scope w brand a packet.selected.selected p got
      (member,.typeDecl shape) here
  cases kind with
  | associated cs sh formed =>
    have belongs := (GeneralSourceRoleCstTypeRules293.type_exact ..).mp formed
    obtain ⟨children,rfl⟩ := type_evidence_original_node transfer belongs
    exact ⟨role,name,value,children,b,st,leaf,witness,read,place,atRaw⟩

end Yulang.GeneralSourceRoleCstCoverageEnd295
