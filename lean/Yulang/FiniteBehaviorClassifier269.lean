import Yulang.FiniteBehaviorCatalogue269
import Yulang.FiniteBehaviorSimulation269

namespace Yulang.FiniteBehaviorClassifier269
open FiniteRankBehavior269 (Code Tracks catalogue universe_zero universe_succ)

structure Basis (Source Label : Type) where
 observe : Source → Label
 move : Source → Source → Prop
 rank : Source → Nat
 labels : List Label
 supported : ∀ source, observe source ∈ labels
 decreases : ∀ before after, move before after → rank after < rank before

/-- This is a mathematically well-defined classifier. It uses classical
existential filtering of the concrete successor relation, so no executable
classifier is claimed. Its output is a finite standalone executable code. -/
noncomputable def classify (basis : Basis Source Label) (source : Source) : Code Label := by
 classical
 exact .node (basis.observe source)
   ((catalogue basis.labels (basis.rank source - 1)).filter fun candidate =>
     decide (∃ successor : {s // basis.move source s}, classify basis successor.val = candidate))
termination_by basis.rank source
decreasing_by exact basis.decreases _ _ successor.property

theorem classifier_label (basis : Basis Source Label) (source : Source) :
 (classify basis source).label = basis.observe source := by
 rw [classify]
 rfl

theorem in_catalogue (basis : Basis Source Label) (source : Source) :
 classify basis source ∈ catalogue basis.labels (basis.rank source) := by
 classical
 cases rank : basis.rank source with
 | zero =>
   have empty : (catalogue basis.labels (basis.rank source - 1)).filter
        (fun candidate => decide (∃ successor : {s // basis.move source s},
          classify basis successor.val = candidate)) = [] := by
     apply List.eq_nil_iff_forall_not_mem.mpr
     intro item listed
     obtain ⟨w,_⟩ := of_decide_eq_true (List.mem_filter.mp listed).2
     have impossible := basis.decreases source w.val w.property
     omega
   rw [classify,empty]
   exact (universe_zero ..).mpr (basis.supported source)
 | succ depth =>
   rw [classify]
   apply (universe_succ ..).mpr
   refine ⟨basis.supported source,?_⟩
   rw [rank,Nat.succ_sub_one]
   exact List.filter_sublist ..

theorem child_iff (basis : Basis Source Label) (source : Source) (code : Code Label) :
 code ∈ (classify basis source).children ↔
 ∃ after, basis.move source after ∧ classify basis after = code := by
 classical
 have eq : (classify basis source).children =
    (catalogue basis.labels (basis.rank source-1)).filter
      (fun candidate => decide (∃ successor : {s // basis.move source s},classify basis successor.val = candidate)) := by
   rw [classify]
   rfl
 rw [eq,List.mem_filter,decide_eq_true_eq]
 constructor
 · rintro ⟨_,⟨after,ends⟩⟩
   exact ⟨after.val,after.property,ends⟩
 · rintro ⟨after,step,ends⟩
   have shorter := basis.decreases source after step
   have allowed := (FiniteBehaviorCatalogue269.mono basis.labels
     (show basis.rank after ≤ basis.rank source-1 by omega)).subset (in_catalogue basis after)
   exact ⟨ends ▸ allowed,⟨⟨after,step⟩,ends⟩⟩

theorem finite (basis : Basis Source Label) (bound : Nat) (source : Source) (within : basis.rank source ≤ bound) :
 classify basis source ∈ catalogue basis.labels bound :=
 (FiniteBehaviorCatalogue269.mono basis.labels within).subset (in_catalogue basis source)

theorem transfer_step (basis : Basis Source Label) {one two after : Source}
 (same : classify basis one = classify basis two) (step : basis.move one after) :
 ∃ companion, basis.move two companion ∧ classify basis after = classify basis companion := by
 have member := (child_iff basis one _).mpr ⟨after,step,rfl⟩
 rw [same] at member
 obtain ⟨companion,moved,same⟩ := (child_iff basis two _).mp member
 exact ⟨companion,moved,same.symm⟩

theorem terminal_iff (basis : Basis Source Label) (source : Source) :
 (classify basis source).children = [] ↔ ∀ after, ¬ basis.move source after := by
 rw [List.eq_nil_iff_forall_not_mem]
 constructor
 · intro absent after step
   exact absent _ ((child_iff basis source _).mpr ⟨after,step,rfl⟩)
 · intro quiet child member
   obtain ⟨after,move,_⟩ := (child_iff basis source child).mp member
   exact quiet after move

end Yulang.FiniteBehaviorClassifier269
