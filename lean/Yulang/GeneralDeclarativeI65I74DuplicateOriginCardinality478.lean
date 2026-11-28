import Yulang.GeneralDeclarativeI65I74OriginalPoseSegments478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarationPatterns (Pattern normalize merge)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose atSource literal_occurrence)

def duplicateOriginal478 : Nat → Pattern → Pattern
  | 0, p => p
  | Nat.succ k, p => .join (duplicateOriginal478 k p) (duplicateOriginal478 k p)

def binaryJoinPaths478 : Nat → List (List Pose)
  | 0 => [[]]
  | Nat.succ k => (binaryJoinPaths478 k).map (Pose.left :: ·) ++
      (binaryJoinPaths478 k).map (Pose.right :: ·)

theorem every_equal_join_level_collapses_to_one_normalized_tree478
    (k : Nat) (p : Pattern) :
    normalize (duplicateOriginal478 k p) = normalize p := by
  induction k with
  | zero => rfl
  | succ k ih => simp [duplicateOriginal478,normalize,ih,merge]

private theorem map_nodup_of_injective478 {α β : Type} (f : α → β)
    {xs : List α} (unique : xs.Nodup)
    (inject : ∀ x y, f x=f y → x=y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    obtain ⟨outside,restUnique⟩ := List.nodup_cons.mp unique
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih restUnique⟩
    intro impossible
    obtain ⟨y,inRest,same⟩ := List.mem_map.mp impossible
    exact outside ((inject y x same) ▸ inRest)

theorem complete_binary_original_positions_are_distinct478 (k : Nat) :
    (binaryJoinPaths478 k).Nodup := by
  induction k with
  | zero => simp [binaryJoinPaths478]
  | succ k ih =>
    apply List.nodup_append.mpr
    refine ⟨?_,?_,?_⟩
    · exact map_nodup_of_injective478 _ ih (by intro a b eq; exact (List.cons.inj eq).2)
    · exact map_nodup_of_injective478 _ ih (by intro a b eq; exact (List.cons.inj eq).2)
    · intro a ha b hb same
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨_,_,rfl⟩ := List.mem_map.mp hb
      cases same

theorem there_are_two_to_the_depth_many_binary_original_positions478 (k : Nat) :
    (binaryJoinPaths478 k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [binaryJoinPaths478,List.length_append,List.length_map,List.length_map,ih,Nat.pow_succ]
    omega

theorem every_duplicate_branch_keeps_a_genuine_literal_original_occurrence478
    {p sub : Pattern} {action : Address} {original : List Pose}
    (h : WrittenPattern460.PhysicalOrigin.Origin p action original sub)
    (k : Nat) {branch : List Pose} (inBranch : branch ∈ binaryJoinPaths478 k) :
    WrittenPattern460.PhysicalOrigin.Origin (duplicateOriginal478 k p) action (branch ++ original) sub := by
  induction k generalizing branch with
  | zero =>
    have ni : branch = [] := by simpa [binaryJoinPaths478] using inBranch
    subst branch
    exact h
  | succ k ih =>
    rcases List.mem_append.mp inBranch with hit|hit
    · obtain ⟨before,old,rfl⟩ := List.mem_map.mp hit
      exact .left rfl (ih old)
    · obtain ⟨before,old,rfl⟩ := List.mem_map.mp hit
      exact .right rfl (ih old)

theorem one_normalized_tree_has_exponentially_many_distinct_origins478
    {p sub : Pattern} {action : Address} {original : List Pose}
    (h : WrittenPattern460.PhysicalOrigin.Origin p action original sub) (k : Nat) :
    ∃ all : List (List Pose), all.Nodup ∧ all.length = 2^k ∧
      (∀ pose ∈ all, WrittenPattern460.PhysicalOrigin.Origin (duplicateOriginal478 k p) action pose sub ∧
        atSource (duplicateOriginal478 k p) pose = some sub) ∧
      normalize (duplicateOriginal478 k p) = normalize p := by
  let all := (binaryJoinPaths478 k).map (· ++ original)
  refine ⟨all,map_nodup_of_injective478 _ (complete_binary_original_positions_are_distinct478 k) ?_,
    by simp [all,there_are_two_to_the_depth_many_binary_original_positions478],?_,
    every_equal_join_level_collapses_to_one_normalized_tree478 k p⟩
  · intro a b eq
    exact List.append_cancel_right eq
  · intro pose present
    obtain ⟨branch,source,rfl⟩ := List.mem_map.mp present
    have hit := every_duplicate_branch_keeps_a_genuine_literal_original_occurrence478 h k source
    exact ⟨hit,literal_occurrence hit⟩



private theorem coded_positions_still_distinct478 {α β : Type} (f : α → β)
    {xs : List α} (unique : xs.Nodup)
    (inject : ∀ x ∈ xs, ∀ y ∈ xs, f x=f y → x=y) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    obtain ⟨outside,restUnique⟩ := List.nodup_cons.mp unique
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih restUnique (fun a ha b hb => inject a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩
    intro impossible
    obtain ⟨y,inRest,same⟩ := List.mem_map.mp impossible
    exact outside ((inject y (List.mem_cons_of_mem _ inRest) x List.mem_cons_self same) ▸ inRest)

private theorem length_le_of_nodup_subset478 {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α} (unique : xs.Nodup) (subset : ∀ a ∈ xs, a ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a rest ih =>
    obtain ⟨off,remaining⟩ := List.nodup_cons.mp unique
    have one := subset a List.mem_cons_self
    have strip : ∀ x ∈ rest, x ∈ ys.erase a := by
      intro x hit
      have different : x ≠ a := fun same => off (same ▸ hit)
      exact (List.mem_erase_of_ne different).mpr (subset x (List.mem_cons_of_mem _ hit))
    have hh := ih remaining strip
    rw [List.length_erase_of_mem one] at hh
    have pos := List.length_pos_of_mem one
    simp only [List.length_cons]
    omega

theorem exact_origin_decoder_needs_a_distinct_token_for_each_normalized_away_branch478
    (k m : Nat) (original : List Pose)
    (encode : List Pose → Fin m) (decode : Fin m → List Pose)
    (correct : ∀ branch ∈ binaryJoinPaths478 k, decode (encode (branch ++ original)) = branch ++ original) :
    2^k ≤ m := by
  let tok := fun branch : List Pose => encode (branch ++ original)
  have inj : ∀ b ∈ binaryJoinPaths478 k, ∀ c ∈ binaryJoinPaths478 k, tok b=tok c → b=c := by
    intro b hb c hc equal
    have eq := congrArg decode equal
    change decode (encode (b ++ original)) = decode (encode (c ++ original)) at eq
    rw [correct b hb,correct c hc] at eq
    exact List.append_cancel_right eq
  have unique := coded_positions_still_distinct478 tok (complete_binary_original_positions_are_distinct478 k) inj
  have fits := length_le_of_nodup_subset478 unique (ys := List.finRange m) (by intro a _; exact List.mem_finRange a)
  simpa only [List.length_map,List.length_finRange,there_are_two_to_the_depth_many_binary_original_positions478] using fits

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

