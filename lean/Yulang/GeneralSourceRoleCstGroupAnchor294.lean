import Yulang.GeneralSourceRoleCstCleanBoundary294

/-! Locate a supplied ErrorGroup range by unique matching to original
portable runs. This does not create or collect Rust diagnostics. -/
namespace Yulang.GeneralSourceRoleCstGroupAnchor294
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstWire293 (Wire Transfer)
open GeneralSourceRoleCstOriginalMarks294 (Origin original Element original_exact)
open GeneralSourceRoleCstErrorRuns294 (runs TokenRun every_run runs_flatten)
open GeneralSourceRoleCstRunExtent294 (extent)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstMarkScope294 (Zone classify unrelated_exact)

def isOriginalError (mark : Origin) : Bool :=
  mark.originalTag == "Error" && mark.originalMode == .token

def matchRange (range : Extent) (row : List Origin) : Bool :=
  decide (extent row = some range) && row.all isOriginalError

def candidates (wire : Wire) (tree : Tree) (range : Extent) : List (List Origin) :=
  (runs (original wire tree)).filter (matchRange range)

def unique (wire : Wire) (tree : Tree) (range : Extent) : Option (List Origin) :=
  match candidates wire tree range with
  | [row] => some row
  | _ => none

theorem unique_exact (wire : Wire) (tree : Tree) (r : Extent) (row : List Origin) :
    unique wire tree r = some row ↔ candidates wire tree r = [row] := by
  cases found : candidates wire tree r with
  | nil => simp [unique,found]
  | cons x xs =>
    cases xs with
    | nil => simp [unique,found]
    | cons b rest => simp [unique,found]

theorem candidate_exact (wire : Wire) (tree : Tree) (r : Extent) (row : List Origin) :
    row ∈ candidates wire tree r ↔
      row ∈ runs (original wire tree) ∧ extent row = some r ∧
      ∀ o ∈ row, o.originalTag = "Error" ∧ o.originalMode = .token := by
  simp [candidates,matchRange,isOriginalError,List.mem_filter,Bool.and_eq_true,
    List.all_eq_true]

theorem unique_has_run (wire : Wire) (tree : Tree) (r : Extent) (row : List Origin)
    (chosen : unique wire tree r = some row) : TokenRun row ∧ extent row = some r := by
  have hit : row ∈ candidates wire tree r := by rw [(unique_exact ..).mp chosen]; exact List.mem_cons_self
  obtain ⟨onList,e,_⟩ := (candidate_exact ..).mp hit
  exact ⟨every_run _ _ onList,e⟩

theorem origin_for_each {wire : Wire} {tree : Tree} (mapping : Transfer wire tree)
    {range : Extent} {row : List Origin} (picked : unique wire tree range = some row)
    {o : Origin} (h : o ∈ row) :
    ∃ text, GeneralSourceRoleCstWirePaths293.atWire o.occurrence.path wire =
      some (.token "Error" text) := by
  have hit : row ∈ candidates wire tree range := by rw [(unique_exact ..).mp picked]; exact List.mem_cons_self
  obtain ⟨inRuns,_,all⟩ := (candidate_exact ..).mp hit
  have inAll : o ∈ (runs (original wire tree)).flatten := List.mem_flatten.mpr ⟨row,inRuns,h⟩
  rw [runs_flatten] at inAll
  obtain ⟨raw,t,atRaw,extent,related,kind,bad,tag⟩ := (original_exact wire tree mapping o).mp inAll
  have tags := all o h
  cases raw with
  | node k cs =>
    have shape := (Prod.mk.inj tag).2
    rw [tags.2] at shape
    cases shape
  | token label text =>
    have shape := (Prod.mk.inj tag).1
    change label = o.originalTag at shape
    exact ⟨text,shape.trans tags.1 ▸ atRaw⟩

def outside (s : Path) (row : List Origin) : Bool :=
  row.all (fun item => classify s item.occurrence.path == .unrelated)

theorem outside_exact (s : Path) (row : List Origin) :
    outside s row = true ↔ ∀ item ∈ row,
      ¬ s <+: item.occurrence.path ∧ ¬ item.occurrence.path <+: s := by
  simp [outside,List.all_eq_true,unrelated_exact]

end Yulang.GeneralSourceRoleCstGroupAnchor294
