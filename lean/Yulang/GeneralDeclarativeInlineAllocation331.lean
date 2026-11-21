import Yulang.GeneralDeclarativeInlineTrace331
import Yulang.GeneralDeclarativeRecordPoints330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineAllocation331
open GeneralDeclarativeHead320 (State Equation environment)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)
open GeneralDeclarativeTermOccurrences322 (actual_positions)
open GeneralDeclarativeRecordPoints330 (expanded fieldName stepName)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeNewNames321 (numbered)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr values)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm record_congr variant_congr union_congr)
open GeneralNominalCenteredHeadMatCompilerSemantics (primitive_congr nominal_congr)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalMatchedAssembly (Aligned)
open CommonNominalFullCarrier (Equivalent)

def jobs (seen : List Occurrence) : List Expr := seen.flatMap (fun o => expanded o.term)

def next (start : Nat) (seen : List Occurrence) : Nat := start + (jobs seen).length

def renamed (start : Nat) : List Occurrence → List Occurrence
  | [] => []
  | o::os => ⟨o.binder,o.mode,.variable (fieldName o.term start)⟩ ::
      renamed (stepName o.term start) os

def captures (start : Nat) : List Occurrence → List (Nat × Capture)
  | [] => []
  | o::os => (o.binder,point (fieldName o.term start)) ::
      captures (stepName o.term start) os

theorem bounded (s : State) (start : Nat) (seen : List Occurrence) :
    ∀ p ∈ captures start seen, Bounds s p.2 := by
  induction seen generalizing start with
  | nil => intro p h; cases h
  | cons o os ih =>
    intro p h
    rcases List.mem_cons.mp h with rfl|rest
    · exact point_bounded _ _
    · exact ih _ _ rest

theorem actual_capture (start : Nat) (seen : List Occurrence)
    (actual : ∀ o ∈ seen, o.mode = .actual) :
    renamed start seen = occurrences (captures start seen) := by
  induction seen generalizing start with
  | nil => rfl
  | cons o os ih =>
    have h := actual o List.mem_cons_self
    simp only [renamed,captures,occurrences,List.map_cons,h,ih _
      (fun x haveIt => actual x (List.mem_cons_of_mem _ haveIt))]
    rfl

theorem renamed_append (start : Nat) (first last : List Occurrence) :
    renamed start (first++last) = renamed start first ++ renamed (next start first) last := by
  induction first generalizing start with
  | nil => simp [next,jobs,renamed]
  | cons o os ih =>
    simp only [List.cons_append,renamed,ih]
    have eq : next (stepName o.term start) os = next start (o::os) := by
      simp [next,stepName,jobs,Nat.add_assoc]
    rw [eq]

theorem numbered_append (start : Nat) (xs ys : List Expr) :
    numbered start (xs++ys) = numbered start xs ++ numbered (start+xs.length) ys := by
  induction xs generalizing start with
  | nil => simp [numbered]
  | cons x xs ih =>
    simp only [List.cons_append,numbered,ih,List.length_cons]
    have eq : start + 1 + xs.length = start + (xs.length + 1) := by omega
    rw [eq]

def Sound (m : Assignment) (start : Nat) (uses : List Occurrence) : Prop :=
  ∀ e ∈ numbered start (jobs uses), Holds m e

theorem split_sound {m : Assignment} {start : Nat} {one two : List Occurrence}
    (h : Sound m start (one++two)) : Sound m start one ∧ Sound m (next start one) two := by
  simp only [Sound,jobs,List.flatMap_append,numbered_append] at h
  exact ⟨fun e seen => h e (List.mem_append_left _ seen),fun e seen => h e (List.mem_append_right _ seen)⟩

theorem one_name (m : Assignment) (start : Nat) (o : Occurrence)
    (valid : Sound m start [o]) : eqAt m o.term (.variable (fieldName o.term start)) := by
  rcases o with ⟨key,mode,e⟩
  cases e
  case «variable» => exact eqv_refl _
  all_goals exact eqv_symm (valid _ List.mem_cons_self)

/-- The name-bearing walk is fixed by the source occurrence list and
the fresh seed. Every model satisfying the ordinary name batch sees
the same old and new terms. No witness is selected by a model. -/
theorem name_walk (known : Walk mode raw code uses) (seed : Nat) :
    ∃ rebuilt, (∀ m, Sound m seed uses → eqAt m raw rebuilt) ∧
      Walk mode rebuilt code (renamed seed uses) := by
  refine Walk.rec
    (motive_1 := fun mode raw code uses _ => ∀ n, ∃ rebuilt,
      (∀ m, Sound m n uses → eqAt m raw rebuilt) ∧ Walk mode rebuilt code (renamed n uses))
    (motive_2 := fun mode raw code uses _ => ∀ n, ∃ rebuilt,
      (∀ m, Sound m n uses → Aligned Equivalent
        (values (environment m) .actual raw) (values (environment m) .actual rebuilt)) ∧
      WalkMany mode rebuilt code (renamed n uses))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ known seed
  · intro mode raw binder n
    exact ⟨_,fun m fit => one_name m n ⟨binder,mode,raw⟩ fit,.capture⟩
  · intro mode as bs seen tag _ ih n
    obtain ⟨out,truth,walk⟩ := ih n
    exact ⟨.primitive tag out,fun m h => primitive_congr _ (truth m h),.primitive walk⟩
  · intro as bs seen mode tag _ ih n
    obtain ⟨out,truth,walk⟩ := ih n
    exact ⟨.nominal tag out,fun m h => nominal_congr _ (truth m h),.nominal walk⟩
  · intro mode a b first x y last key _ _ ih jh n
    obtain ⟨u,p,w⟩ := ih n
    obtain ⟨v,q,z⟩ := jh (next n first)
    exact ⟨.record key u v,fun m h => record_congr key (p m (split_sound h).1) (q m (split_sound h).2),
      (renamed_append n first last).symm ▸ Walk.record w z⟩
  · intro mode a b seen tag _ ih n
    obtain ⟨out,truth,walk⟩ := ih n
    exact ⟨.variant tag out,fun m h => variant_congr _ (truth m h),.variant walk⟩
  · intro mode a b first x y last _ _ ih jh n
    obtain ⟨u,p,w⟩ := ih n
    obtain ⟨v,q,z⟩ := jh (next n first)
    exact ⟨.join u v,fun m h => union_congr (p m (split_sound h).1) (q m (split_sound h).2),
      (renamed_append n first last).symm ▸ Walk.join w z⟩
  · intro mode n
    exact ⟨[],fun _ _ => .nil,.nil⟩
  · intro mode a b first as bs last _ _ ih jh n
    obtain ⟨u,p,w⟩ := ih n
    obtain ⟨v,q,z⟩ := jh (next n first)
    exact ⟨u::v,fun m h => .cons (p m (split_sound h).1) (q m (split_sound h).2),
      (renamed_append n first last).symm ▸ WalkMany.cons w z⟩

end Yulang.GeneralDeclarativeInlineAllocation331
