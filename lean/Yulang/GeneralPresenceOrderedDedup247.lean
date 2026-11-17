import Yulang.GeneralPresenceOrderedSupport247
import Yulang.GeneralPresenceOwnerRewrite244

/-! Keep-first removal of duplicate target entries, preserving relative order.
Semantic preservation requires coherent duplicate RHSs; conflicting duplicate
definitions cannot be discarded. The actual source adapter remains separate. -/
namespace Yulang.GeneralPresenceOrderedDedup247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceUsedSupport245
variable {Name : Type} [DecidableEq Name]

def remainder (head : Entry Name) (rest : List (Entry Name)) : List (Entry Name) :=
  rest.filter (fun entry => decide (entry.1 ≠ head.1))

def dedup (entries : List (Entry Name)) : List (Entry Name) :=
  match entries with
  | [] => []
  | head :: rest => head :: dedup (remainder head rest)
termination_by entries.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem remainder_subset (head : Entry Name) (rest : List (Entry Name)) : remainder head rest ⊆ rest := by
  intro entry member
  exact (List.mem_filter.mp member).1

theorem dedup_subset (entries : List (Entry Name)) : dedup entries ⊆ entries := by
  cases entries with
  | nil => simp [dedup]
  | cons head rest =>
    rw [dedup]
    intro entry member
    rcases List.mem_cons.mp member with rfl | present
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (remainder_subset head rest (dedup_subset (remainder head rest) present))
termination_by entries.length
decreasing_by
  all_goals simp_all only [List.length_cons]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem dedup_sublist (entries : List (Entry Name)) : List.Sublist (dedup entries) entries := by
  cases entries with
  | nil => simp [dedup]
  | cons head rest =>
    rw [dedup]
    exact List.Sublist.cons_cons head ((dedup_sublist (remainder head rest)).trans List.filter_sublist)
termination_by entries.length
decreasing_by
  all_goals simp_all only [List.length_cons]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

omit [DecidableEq Name] in
theorem coherent_subset (first last : List (Entry Name)) (subset : first ⊆ last)
    (coherent : Coherent last) : Coherent first :=
  fun a am b bm same => coherent a (subset am) b (subset bm) same

theorem member_preserved (entries : List (Entry Name)) (coherent : Coherent entries)
    (entry : Entry Name) (member : entry ∈ entries) : entry ∈ dedup entries := by
  cases entries with
  | nil => simp at member
  | cons head rest =>
    rw [dedup]
    by_cases same : entry.1 = head.1
    · have rhs := coherent entry member head (by simp) same
      have equal : entry = head := Prod.ext same rhs
      exact List.mem_cons.mpr (Or.inl equal)
    · have present : entry ∈ rest := by
        rcases List.mem_cons.mp member with equal | present
        · exact False.elim (same (congrArg Prod.fst equal))
        · exact present
      have kept : entry ∈ remainder head rest := by simp [remainder,present,same]
      have subset : remainder head rest ⊆ head :: rest :=
        fun _ member => List.mem_cons_of_mem _ (remainder_subset head rest member)
      exact List.mem_cons_of_mem _ (member_preserved (remainder head rest)
        (coherent_subset _ _ subset coherent) entry kept)
termination_by entries.length
decreasing_by
  all_goals simp_all only [List.length_cons]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem targets_nodup (entries : List (Entry Name)) : ((dedup entries).map Prod.fst).Nodup := by
  cases entries with
  | nil => simp [dedup]
  | cons head rest =>
    rw [dedup,List.map_cons,List.nodup_cons]
    refine ⟨?_,targets_nodup (remainder head rest)⟩
    intro member
    obtain ⟨entry,present,equal⟩ := List.mem_map.mp member
    have kept := dedup_subset (remainder head rest) present
    have different : entry.1 ≠ head.1 := by simpa [remainder] using (List.mem_filter.mp kept).2
    exact different equal
termination_by entries.length
decreasing_by
  all_goals simp_all only [List.length_cons]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem block_all_iff (model : Model) (assignment : Name → Comp model)
    (entries : List (Entry Name)) (coherent : Coherent entries) :
    All model assignment (block (dedup entries)) ↔ All model assignment (block entries) := by
  constructor
  · intro valid atom member
    obtain ⟨entry,present,contained⟩ := List.mem_flatMap.mp member
    exact valid atom (List.mem_flatMap.mpr ⟨entry,member_preserved entries coherent entry present,contained⟩)
  · intro valid atom member
    obtain ⟨entry,present,contained⟩ := List.mem_flatMap.mp member
    exact valid atom (List.mem_flatMap.mpr ⟨entry,dedup_subset entries present,contained⟩)

theorem typed_pool_preserved (entries : List (Entry Name)) (pool : List Name)
    (covered : ∀ rhs ∈ entries, ∀ name ∈ typedReads rhs.2, name ∈ pool) :
    ∀ rhs ∈ dedup entries, ∀ name ∈ typedReads rhs.2, name ∈ pool :=
  fun rhs member => covered rhs (dedup_subset entries member)

theorem safe_pool (entries : List (Entry Name)) (pool : List Name)
    (protectedTargets : ∀ target ∈ entries, target.1 ∉ pool)
    (coveredReads : ∀ rhs ∈ entries, ∀ name ∈ typedReads rhs.2, name ∈ pool) :
    SafeOrder (dedup entries) :=
  GeneralPresenceOrderedSupport247.safe_pool (dedup entries) pool (targets_nodup entries)
    (fun target member => protectedTargets target (dedup_subset entries member))
    (typed_pool_preserved entries pool coveredReads)

end Yulang.GeneralPresenceOrderedDedup247
