import Yulang.GeneralSourceRoleCstMarkUnique294

/-! Computing spans and restoring the original labels retains all marked
addresses in order, for an exactly decoded wire. -/
namespace Yulang.GeneralSourceRoleCstPathFidelity294
open GeneralSourceRoleCstTree293 (Path Tree Kind)
open GeneralSourceRoleCstMarkUnique294 (paths marks_paths_nodup)
open GeneralSourceRoleCstMarks294 (marks marks_exact)
open GeneralSourceRoleCstMarkSpans294 (Entry attach entries reach_has_extent entry_exact)
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstOriginalMarks294 (Origin attachOriginal original tagAndMode)
open GeneralSourceRoleCstWirePaths293 (transfer_path)
open GeneralSourceRoleCstSpan293 (locate locate_tree)
open GeneralSourceRoleCstPath293 (follow)

theorem ordered_path_map {α β : Type} (read : α → Option β) (input : List α)
    (start : α → Path) (out : β → Path)
    (correct : ∀ a ∈ input, ∃ b, read a = some b ∧ out b = start a) :
    (input.filterMap read).map out = input.map start := by
  induction input with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨b,r,eq⟩ := correct head List.mem_cons_self
    have tailEq := ih (fun a found => correct a (List.mem_cons_of_mem _ found))
    simp only [List.filterMap_cons_some r,List.map_cons,eq,tailEq]

theorem entries_same_paths (root : Tree) :
    (entries root).map Entry.path = paths (marks root) := by
  unfold entries paths
  apply ordered_path_map
  rintro ⟨p,k⟩ found
  obtain ⟨node,here,_,_⟩ := (marks_exact ..).mp found
  obtain ⟨span,located⟩ := reach_has_extent here
  exact ⟨⟨p,k,span⟩,by simp [attach,located],rfl⟩

theorem original_same_paths (wire : Wire) (tree : Tree) (map : Transfer wire tree) :
    (original wire tree).map (fun o => o.occurrence.path) = paths (marks tree) := by
  rw [← entries_same_paths]
  unfold original
  apply ordered_path_map
  intro e mem
  obtain ⟨node,loc,_,_⟩ := (entry_exact ..).mp mem
  have here : follow e.path tree = some node := by rw [←locate_tree _ _ 0,loc]; rfl
  obtain ⟨raw,atRaw,_⟩ := (transfer_path map e.path node).mp here
  exact ⟨⟨e,(tagAndMode raw).1,(tagAndMode raw).2⟩,by simp [attachOriginal,atRaw],rfl⟩

theorem original_paths_nodup (wire : Wire) (tree : Tree) (map : Transfer wire tree) :
    ((original wire tree).map (fun o => o.occurrence.path)).Nodup := by
  rw [original_same_paths wire tree map]
  exact marks_paths_nodup tree

theorem original_count (wire : Wire) (tree : Tree) (map : Transfer wire tree) :
    (original wire tree).length = (marks tree).length := by
  simpa [paths] using congrArg List.length (original_same_paths wire tree map)

end Yulang.GeneralSourceRoleCstPathFidelity294
