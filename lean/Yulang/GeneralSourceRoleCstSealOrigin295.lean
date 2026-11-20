import Yulang.GeneralSourceRoleCstSelectedSeal295

namespace Yulang.GeneralSourceRoleCstSealOrigin295
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstSnapshot293 (Address Snapshot mark)
open GeneralSourceRoleCstSelectedSeal295 (Selection select select_exact)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleCstRustSnapshot293 (exportAt export_exact)
open GeneralSourceRoleCstRustRole293 (extract extract_exact)
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleCstVisibleReceipt294 (project_exact)
open GeneralSourceRoleCstMixedReceipt294 (export_exact)
open GeneralSourceRoleCstWirePaths293 (atWire transfer_path)

theorem kept_export {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (packet : Selection Brand) (out : Tracked Scope (Address Brand))
    (accepted : select policy scope w brand a packet = some out) :
    ∃ root, Transfer w root ∧
      GeneralSourceRoleCstRustSnapshot293.exportAt scope ⟨brand,root⟩ a = some out := by
  have projected := ((select_exact ..).mp accepted).2.2.2
  obtain ⟨strict,_⟩ := (project_exact ..).mp projected
  obtain ⟨root,events,conversion,_,_,_,kept⟩ :=
    (GeneralSourceRoleCstMixedReceipt294.export_exact ..).mp strict
  exact ⟨root,conversion,kept⟩

theorem selected_site {Scope Brand : Type} [DecidableEq Brand] (policy : Policy)
    (scope : Scope) (w : Wire) (brand : Brand) (a : Address Brand)
    (packet : Selection Brand) (out : Tracked Scope (Address Brand))
    (accepted : select policy scope w brand a packet = some out) :
    out.atRole = a ∧ a = packet.address ∧ ∃ role raw,
      atWire a.path w = some raw ∧ Transfer raw role := by
  obtain ⟨root,conversion,kept⟩ := kept_export policy scope w brand a packet out accepted
  obtain ⟨chosen,t,tracked,picked,found,eq⟩ :=
    (GeneralSourceRoleCstRustSnapshot293.export_exact ..).mp kept
  obtain ⟨head,j,name,params,children,node,headOK,scopeOK,addressOf,shape,body⟩ :=
    (extract_exact ..).mp found
  obtain ⟨raw,wire,relation⟩ := (transfer_path conversion a.path t).mp picked
  refine ⟨?_,((select_exact ..).mp accepted).1,t,raw,wire,relation⟩
  rw [← eq]
  cases a
  simp only [mark,addressOf]
  exact congrArg (fun b => Address.mk b _) chosen.symm

end Yulang.GeneralSourceRoleCstSealOrigin295
