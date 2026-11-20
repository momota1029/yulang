import Yulang.GeneralSourceRoleCstMarkPolicy294

/-! The report never turns a selected role into a certified whole file.
Candidate projection, scoped mark flags, and optional admission are distinct. -/
namespace Yulang.GeneralSourceRoleCstMarkReport294
open GeneralSourceRoleCstTree293 (Tree Path Kind)
open GeneralSourceRoleCstMarks294 (marks marks_exact)
open GeneralSourceRoleCstMarkSpans294 (Entry entries entry_exact mark_has_entry)
open GeneralSourceRoleCstMarkScope294 (Zone classify)
open GeneralSourceRoleCstMarkPolicy294 (Policy allows BranchPlain branch_exact guarded)
open GeneralSourceRoleCstRecovery293 (Plain)
open GeneralSourceRoleCstSnapshot293 (Address Snapshot)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleTrack292 (Tracked)

theorem entries_empty (root : Tree) : entries root = [] ↔ marks root = [] := by
  constructor
  · intro none
    cases e : marks root with
    | nil => rfl
    | cons m ms =>
      obtain ⟨p,k⟩ := m
      have h : (p,k) ∈ marks root := by simp [e]
      obtain ⟨q,has,_,_⟩ := mark_has_entry root p k h
      rw [none] at has
      cases has
  · intro h
    simp [entries,h]

theorem entries_branch_exact (root : Tree) (s : Path) :
    ((entries root).all fun x => classify s x.path == .unrelated) = true ↔ BranchPlain root s := by
  rw [List.all_eq_true]
  constructor
  · intro h p k mem
    obtain ⟨e,listed,rfl,rfl⟩ := mark_has_entry root p k mem
    exact (GeneralSourceRoleCstMarkScope294.unrelated_exact ..).mp (beq_iff_eq.mp (h e listed))
  · intro h e listed
    obtain ⟨node,read,tag,bad⟩ := (entry_exact ..).mp listed
    have reach : GeneralSourceRoleCstPath293.follow e.path root = some node := by
      rw [← GeneralSourceRoleCstSpan293.locate_tree _ _ 0,read]
      rfl
    have mem := (marks_exact ..).mpr ⟨node,reach,tag,bad⟩
    exact beq_iff_eq.mpr ((GeneralSourceRoleCstMarkScope294.unrelated_exact ..).mpr (h _ _ mem))

structure Report (Scope Brand : Type) where
  found : List (Zone × Entry)
  wholeWireMarkFree : Bool
  selectedBranchMarkFree : Bool
  projected : Option (Tracked Scope (Address Brand))

def run {Scope Brand : Type} [DecidableEq Brand] (scope : Scope) (s : Snapshot Brand)
    (a : Address Brand) : Report Scope Brand :=
  let all := entries s.root
  ⟨all.map (fun e => (classify a.path e.path,e)),
    all.isEmpty,all.all (fun e => classify a.path e.path == .unrelated),exportAt scope s a⟩

theorem listed_exact {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (z : Zone) (e : Entry) :
    (z,e) ∈ (run scope s a).found ↔
      z = classify a.path e.path ∧
      ∃ node, GeneralSourceRoleCstSpan293.locate e.path s.root 0 = some (node,e.extent) ∧
        node.kind = e.kind ∧ ¬ Plain e.kind := by
  change (z,e) ∈ (entries s.root).map _ ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨r,mem,same⟩
    obtain ⟨tag,rfl⟩ := Prod.mk.inj same
    exact ⟨tag.symm,(entry_exact ..).mp mem⟩
  · rintro ⟨rfl,h⟩
    exact ⟨e,(entry_exact ..).mpr h,rfl⟩

def Report.admitted {Scope Brand : Type} (r : Report Scope Brand) (policy : Policy) :
    Option (Tracked Scope (Address Brand)) :=
  let allowed := match policy with
    | .whole => r.wholeWireMarkFree
    | .selectedBranch => r.selectedBranchMarkFree
  if allowed then r.projected else none

theorem admission_preserved {Scope Brand : Type} [DecidableEq Brand] (scope : Scope)
    (s : Snapshot Brand) (a : Address Brand) (policy : Policy) :
    (run scope s a).admitted policy = guarded policy scope s a := by
  cases policy with
  | whole =>
    have same : (entries s.root).isEmpty = (marks s.root).isEmpty := by
      apply Bool.eq_iff_iff.mpr
      simpa only [List.isEmpty_iff] using entries_empty s.root
    simp [run,Report.admitted,guarded,allows,same] <;> rfl
  | selectedBranch =>
    have same : ((entries s.root).all fun x => classify a.path x.path == .unrelated) =
        GeneralSourceRoleCstMarkPolicy294.branchClear s.root a.path := by
      apply Bool.eq_iff_iff.mpr
      exact (entries_branch_exact ..).trans (branch_exact ..).symm
    simp [run,Report.admitted,guarded,allows,same] <;> rfl

end Yulang.GeneralSourceRoleCstMarkReport294
