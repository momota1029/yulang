import Yulang.GeneralSourceRoleCstExactTags295

/-! Exact original declaration labels on successful role/head selection
and on association readback. Paths denote original mixed children. -/
namespace Yulang.GeneralSourceRoleCstRawType295
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstWirePaths293 (atWire transfer_path)
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleCstSealOrigin295 (kept_export)
open GeneralSourceRoleCstHeadOrigin295 (selected_head_from_original)
open GeneralSourceRoleCstExactTags295 (exact_role_node exact_head_node exact_type_node)
open GeneralSourceRoleCstProducer293 (roleParts)

theorem parts_role_node {t h b : Tree} {i : Nat} (parts : roleParts t = some (h,i,b)) :
    ∃ cs, t = .node .role cs := by
  cases t with
  | token => cases parts
  | node k cs =>
    cases k <;> try cases parts
    exact ⟨cs,rfl⟩

theorem selected_original_role_node {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (out : Tracked S (Address B))
    (accepted : select policy scope w brand a packet = some out) :
    ∃ cs, atWire a.path w = some (.node "RoleDeclaration" cs) := by
  obtain ⟨root,mapping,old⟩ := kept_export policy scope w brand a packet out accepted
  obtain ⟨_,t,tracked,found,extract,_⟩ :=
    (GeneralSourceRoleCstRustSnapshot293.export_exact ..).mp old
  obtain ⟨h,i,n,ps,body,shape,_⟩ :=
    (GeneralSourceRoleCstRustRole293.extract_exact ..).mp extract
  obtain ⟨cs,rfl⟩ := parts_role_node shape
  obtain ⟨raw,atAddress,transfer⟩ := (transfer_path mapping a.path _).mp found
  obtain ⟨ws,rfl⟩ := exact_role_node transfer
  exact ⟨ws,atAddress⟩

theorem selected_original_head_node {S B : Type} [DecidableEq B]
    (policy : Policy) (scope : S) (w : Wire) (brand : B) (a : Address B)
    (packet : Selection B) (out : Tracked S (Address B))
    (accepted : select policy scope w brand a packet = some out) :
    ∃ i cs n ps, atWire (a.path ++ [i]) w = some (.node "TypeExpression" cs) ∧
      out.head = GeneralSourceRoleCstShapes293.toHead n ps := by
  obtain ⟨_,i,raw,t,n,ps,found,related,head,e⟩ :=
    selected_head_from_original policy scope w brand a packet out accepted
  obtain ⟨ts,args,rfl,_,_⟩ := head
  obtain ⟨cs,rfl⟩ := exact_head_node related
  exact ⟨i,cs,n,ps,found,e⟩

theorem type_evidence_original_node {w : Wire} {t : Tree}
    {shape : GeneralSourceRoleSyntaxBoundary292.Shape}
    (exact : Transfer w t) (proof : GeneralSourceRoleCstTypeRules293.IsType t shape) :
    ∃ cs, w = .node "TypeDeclaration" cs := by
  cases proof <;> exact exact_type_node exact

end Yulang.GeneralSourceRoleCstRawType295
