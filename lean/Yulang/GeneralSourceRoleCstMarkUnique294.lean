import Yulang.GeneralSourceRoleCstMixedReceipt294

/-! One enumeration row per raw path. Adjacent rows may have equal byte
intervals, so deduplication by source span would discard information. -/
namespace Yulang.GeneralSourceRoleCstMarkUnique294
open GeneralSourceRoleCstTree293 (Path Tree Kind)
open GeneralSourceRoleCstMarks294 (own marks childMarks child_marks_exact)
open GeneralSourceRoleCstRecovery293 (Plain)

def paths (ms : List (Path × Kind)) : List Path := ms.map Prod.fst

theorem own_paths (k : Kind) : (paths (own k)).Nodup := by
  unfold own
  by_cases h : Plain k
  · rw [ite_eq_left h]; exact List.nodup_nil
  · rw [ite_eq_right h]; exact List.pairwise_singleton _ _

theorem child_path_first (cs : List Tree) (base : Nat) (p : Path)
    (h : p ∈ paths (childMarks base cs)) :
    ∃ i tail, p = (base+i)::tail := by
  obtain ⟨⟨p',k⟩,found,rfl⟩ := List.mem_map.mp h
  obtain ⟨i,tail,_,whereAt,_,_⟩ := (child_marks_exact ..).mp found
  exact ⟨i,tail,whereAt⟩

theorem own_path_nil (k : Kind) (p : Path) (h : p ∈ paths (own k)) : p = [] := by
  by_cases e : Plain k
  · simp [paths,own,e] at h
  · simpa [paths,own,e] using h

theorem prepend_paths (ms : List (Path × Kind)) (n : Nat) :
    paths (ms.map (fun (p,k) => (n::p,k))) = (paths ms).map (List.cons n) := by
  induction ms with
  | nil => rfl
  | cons ms tail ih => cases ms; simp [paths] at ih ⊢

mutual
theorem marks_paths_nodup (root : Tree) : (paths (marks root)).Nodup := by
  cases root with
  | token k str => exact own_paths k
  | node k cs =>
    rw [marks,show paths (own k ++ childMarks 0 cs) =
      paths (own k) ++ paths (childMarks 0 cs) by simp [paths],List.nodup_append]
    refine ⟨own_paths k,child_paths_nodup cs 0,?_⟩
    intro p hp q hq
    have nil := own_path_nil k p hp
    obtain ⟨i,tail,nonempty⟩ := child_path_first cs 0 q hq
    rw [nil,nonempty]
    simp
theorem child_paths_nodup (cs : List Tree) (base : Nat) : (paths (childMarks base cs)).Nodup := by
  cases cs with
  | nil => exact List.nodup_nil
  | cons c cs =>
    rw [childMarks,show ∀ x y, paths (x ++ y) = paths x ++ paths y by simp [paths],
        prepend_paths,List.nodup_append]
    refine ⟨?_,child_paths_nodup cs (base+1),?_⟩
    · exact List.Pairwise.map _ (fun _ _ different same => different (List.cons.inj same).2)
        (marks_paths_nodup c)
    · intro p hp q hq
      obtain ⟨tail,_,rfl⟩ := List.mem_map.mp hp
      obtain ⟨i,other,e⟩ := child_path_first cs (base+1) q hq
      rw [e]
      intro equal
      have bad := (List.cons.inj equal).1
      omega
end

end Yulang.GeneralSourceRoleCstMarkUnique294
