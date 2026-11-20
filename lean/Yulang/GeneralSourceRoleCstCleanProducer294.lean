import Yulang.GeneralSourceRoleCstCleanMembers294

/-! Exact cleanliness of the selected subtree accepted by the existing
wrapped extractor. It does not cover any ancestor or unrelated subtree. -/
namespace Yulang.GeneralSourceRoleCstCleanProducer294
open GeneralSourceRoleCstTree293 (Tree Path significant)
open GeneralSourceRoleCstShapes293 (cleanTree cleanList visible)
open GeneralSourceRoleCstCleanMembers294
open GeneralSourceRoleCstRustHead293 (ActualArgument ActualHead)
open GeneralSourceRoleCstBody293 (IsStatement)
open GeneralSourceRoleCstProducer293 (dropVisibility roleParts)
open GeneralSourceRoleCstRustRole293 (extract extract_exact)
open GeneralSourceRoleCstRecovery293 (TreePlain clean_tree_exact)
open GeneralSourceRoleTrack292 (Tracked)
open GeneralSourceRoleChildCoverage292 (Child)
open GeneralSourceRoleExport292 (Aligned)

theorem argument_clean {t : Tree} {name : String}
    (h : ActualArgument t name) : cleanTree t = true := by
  obtain ⟨cs,inr,rfl,outer,inner⟩ := h
  have innerOK : cleanTree (.node .head inr) = true := by
    apply node_if_clean .head inr (by decide)
    rw [inner]
    rfl
  apply node_if_clean .argument cs (by decide)
  rw [outer]
  change (cleanTree (.node .head inr) && true) = true
  simp [innerOK]

theorem head_clean {t : Tree} {name : String} {ps : List String}
    (h : ActualHead t name ps) : cleanTree t = true := by
  obtain ⟨cs,argv,rfl,picked,aligned⟩ := h
  apply node_if_clean .head cs (by decide)
  rw [picked]
  have args : cleanList argv = true := (each_clean _).mpr (by
    intro arg mem
    obtain ⟨n,_,own⟩ := GeneralSourceRoleManifest292.aligned_left aligned mem
    exact argument_clean own)
  change (true && cleanList argv) = true
  simp [args]

theorem body_clean (base : Path) (cs : List Tree) (outs : List (Path × Child))
    (paired : Aligned (fun p => IsStatement (base ++ [p.1]) p.2) (significant cs) outs) :
    cleanTree (.node .indented cs) = true := by
  apply node_if_clean .indented cs (by decide)
  apply (each_clean _).mpr
  intro x isVisible
  obtain ⟨entry,mem,eq⟩ := List.mem_map.mp isVisible
  obtain ⟨out,_,belongs⟩ := GeneralSourceRoleManifest292.aligned_left paired mem
  exact eq ▸ statement_clean belongs

theorem reinsert_prefix (cs : List (Nat × Tree))
    (proper : cleanList ((dropVisibility cs).map Prod.snd) = true) :
    cleanList (cs.map Prod.snd) = true := by
  cases cs with
  | nil => rfl
  | cons fst rest =>
    obtain ⟨n,x⟩ := fst
    cases x with
    | node => exact proper
    | token kind value =>
      cases kind <;> first | exact proper | simpa [dropVisibility,cleanList,cleanTree] using proper

theorem role_clean {x head body : Tree} {i : Nat} (shape : roleParts x = some (head,i,body))
    (headOK : cleanTree head = true) (bodyOK : cleanTree body = true) : cleanTree x = true := by
  cases x with
  | token => cases shape
  | node k cs =>
    cases k <;> try cases shape
    apply node_if_clean .role cs (by decide)
    unfold visible
    apply reinsert_prefix
    change (match dropVisibility (significant cs) with
      | [(_, .token .roleKw _), (_,lhs), (_, .token .colon _), rhs] => some (lhs,rhs)
      | _ => none) = some (head,i,body) at shape
    generalize formed : dropVisibility (significant cs) = shown at shape
    split at shape
    · rename_i _ jRole word jHead lhs jColon colonValue rhs
      obtain ⟨rfl,other⟩ := Prod.mk.inj (Option.some.inj shape)
      rcases rhs with ⟨j,inner⟩
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj other
      change (true && (cleanTree lhs && (true && (cleanTree inner && true)))) = true
      simp [headOK,bodyOK]
    · cases shape

theorem accepted_subtree_is_plain {Scope : Type} (scope : Scope) (site : Path) (x : Tree)
    (out : Tracked Scope Path) (success : extract scope site x = some out) :
    TreePlain x := by
  obtain ⟨head,j,n,ps,cs,picked,nameOK,owner,path,shape,children⟩ := (extract_exact ..).mp success
  exact (clean_tree_exact x).mp (role_clean picked (head_clean nameOK)
    (body_clean (site ++ [j]) cs out.body children))

end Yulang.GeneralSourceRoleCstCleanProducer294
