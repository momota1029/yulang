import Yulang.GeneralSourceRoleCstRawType295

/-! End-to-end on supplied JSON only. Rows and bytes remain explicit witnesses,
and the external environments/receipts remain scoped hypotheses. -/
namespace Yulang.GeneralSourceRoleCstSelectedEnd295
open Lean (Json)
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstWirePaths293 (atWire)
open GeneralSourceRoleCstJson293 (encode depth)
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstSpan293 (Extent locate)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSelectedJson295 (fromText text_exact)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary checked_exact)
open GeneralSourceRoleCstSelectedCompile295 (compile_origin)
open GeneralSourceRoleCstSelectedRow295 (compile_single_row)
open GeneralSourceRoleCstRawType295 (selected_original_role_node type_evidence_original_node)
open GeneralSourceRoleCstRowExtent295 (read_locates_own_type)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource RoleRow roleTable Valid)

theorem text_exports_one_original_role {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (text : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat)
    (table : RoleSource) (ok : fromText fuel text policy scope brand a packet env fallback = .ok table) :
    ∃ (j : Json) (w : Wire) (children : List Wire) (row : RoleRow) (name : String)
      (arguments : List String),
      Json.parse text = .ok j ∧ encode w = j ∧ depth w ≤ fuel ∧
        a = packet.selected.selected.address ∧ scope = packet.selected.allowedScope ∧
        atWire a.path w = some (.node "RoleDeclaration" children) ∧
        table.rows = [row] ∧ Valid table ∧ row.arity = arguments.length ∧
        (env scope).role name = some row.role := by
  obtain ⟨j,w,parsed,encoded,capacity,finish⟩ := (text_exact ..).mp ok
  obtain ⟨_,built⟩ := (checked_exact ..).mp finish
  obtain ⟨scopeEq,addr,p,site,got,attach⟩ := compile_origin policy scope w brand a packet.selected env fallback table built
  obtain ⟨children,rawRole⟩ := selected_original_role_node policy scope w brand a packet.selected.selected p got
  obtain ⟨_,valid,row,name,args,rows,head,names,arity⟩ :=
    GeneralSourceRoleCstSelectedRow295.tracked_single_row env fallback p table attach
  have scopeOrigin :=
    (GeneralSourceRoleCstHeadOrigin295.selected_head_from_original
      policy scope w brand a packet.selected.selected p got).1
  rw [scopeOrigin] at names
  exact ⟨j,w,children,row,name,args,parsed,encoded,capacity,addr,scopeEq,rawRole,rows,valid,arity,names⟩

theorem text_read_has_raw_type {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (text : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (packet : FiniteBoundary S B) (env : S → Environment) (fallback : Nat)
    (table : RoleSource) (ok : fromText fuel text policy scope brand a packet env fallback = .ok table)
    (role name : Nat) (term : Option Roles.Term) (found : (roleTable table role).assoc name = some term) :
    ∃ (j : Json) (w : Wire) (children : List Wire) (site : Address B)
      (root selected member : Tree) (outer inner : Extent),
      Json.parse text = .ok j ∧ encode w = j ∧ depth w ≤ fuel ∧
        Transfer w root ∧ atWire site.path w = some (.node "TypeDeclaration" children) ∧
        locate a.path root 0 = some (selected,outer) ∧ locate site.path root 0 = some (member,inner) ∧
        outer.low ≤ inner.low ∧ inner.high ≤ outer.high := by
  obtain ⟨j,w,parsed,encoded,capacity,finish⟩ := (text_exact ..).mp ok
  obtain ⟨_,built⟩ := (checked_exact ..).mp finish
  obtain ⟨p,site,shape,root,selected,t,raw,outer,inner,origin,converted,picked,located,
    wireAt,transfer,proof,lo,hi,size⟩ :=
      read_locates_own_type policy scope w brand a packet.selected env fallback table built role name term found
  obtain ⟨children,rfl⟩ := type_evidence_original_node transfer proof
  exact ⟨j,w,children,site,root,selected,t,outer,inner,parsed,encoded,capacity,converted,wireAt,picked,located,lo,hi⟩

end Yulang.GeneralSourceRoleCstSelectedEnd295
