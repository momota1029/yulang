import Yulang.GeneralSourceRoleCstSelectedCompile295

namespace Yulang.GeneralSourceRoleCstSelectedMembers295
open GeneralSourceRoleCstTree293 (Path Tree)
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstSnapshot293 (Address Snapshot mark atAddress address_exact)
open GeneralSourceRoleCstSelectedSeal295 (Selection select)
open GeneralSourceRoleCstSealOrigin295 (kept_export)
open GeneralSourceRoleCstRustSnapshot293 (exportAt export_exact declaration_member_roundtrip)
open GeneralSourceRoleCstRustRole293 (extract_exact)
open GeneralSourceRoleCstBody293 (Classification)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleCstWirePaths293 (atWire transfer_path)

theorem member_prefix {Scope : Type} {scope : Scope} {site : Path} {t : Tree} {out : Tracked Scope Path}
    (chosen : GeneralSourceRoleCstRustRole293.extract scope site t = some out)
    (item : Path × Child) (h : item ∈ out.body) :
    ∃ b stmt leaf, item.1 = site ++ [b,stmt,leaf] := by
  obtain ⟨head,j,n,params,children,shape,read,sc,atSite,hd,aligned⟩ := (extract_exact ..).mp chosen
  obtain ⟨⟨i,s⟩,present,statement⟩ := GeneralSourceRoleManifest292.aligned_right aligned h
  obtain ⟨cs,leaf,child,st,significant,atLeaf,classified⟩ := statement
  exact ⟨j,i,leaf,by simpa [List.append_assoc] using atLeaf⟩

theorem exported_member_prefix {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (value : Tracked Scope (Address Brand))
    (chosen : exportAt scope s a = some value) (item : Address Brand × Child)
    (found : item ∈ value.body) :
    item.1.brand = a.brand ∧ ∃ b stmt leaf, item.1.path = a.path ++ [b,stmt,leaf] := by
  obtain ⟨brandEq,t,payload,picked,extracted,rfl⟩ := (export_exact ..).mp chosen
  obtain ⟨x,belongs,eq⟩ := List.mem_map.mp found
  subst item
  exact ⟨brandEq.symm,member_prefix extracted x belongs⟩

theorem selected_member_is_exact_original {Scope Brand : Type} [DecidableEq Brand]
    (policy : Policy) (scope : Scope) (w : Wire) (brand : Brand) (wanted : Address Brand)
    (packet : Selection Brand) (p : Tracked Scope (Address Brand))
    (picked : select policy scope w brand wanted packet = some p)
    (item : Address Brand × Child) (member : item ∈ p.body) :
    item.1.brand = wanted.brand ∧ (∃ b stmt leaf, item.1.path = wanted.path ++ [b,stmt,leaf]) ∧
      ∃ t raw, atWire item.1.path w = some raw ∧ Transfer raw t ∧ Classification t item.2 := by
  obtain ⟨root,mapping,extracted⟩ := kept_export policy scope w brand wanted packet p picked
  have ⟨b,descends⟩ := exported_member_prefix scope ⟨brand,root⟩ wanted p extracted item member
  obtain ⟨t,loc,shape⟩ :=
    declaration_member_roundtrip scope ⟨brand,root⟩ wanted p extracted item member
  obtain ⟨raw,wire,relation⟩ := (transfer_path mapping item.1.path t).mp ((address_exact ..).mp loc).2
  exact ⟨b,descends,t,raw,wire,relation,shape⟩

end Yulang.GeneralSourceRoleCstSelectedMembers295
