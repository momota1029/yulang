import Yulang.GeneralDeclarativeDeleteShell337

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDeclarativeExactDeleteFinite337
open CommonNominalFullDemand (Ty Observation MaskedProbeStep Environment outerLabels)
open GeneralDeclarativeDeleteShell337 (shell requiredField optionalField required_eq optional_eq)
variable {Row : Type u} {leRow : Row → Row → Prop} {env : Environment Row}
  {order : Ty Row → Ty Row → Prop}

def remaining (keys prior : List Nat) : List Nat := prior.filter fun k => !keys.contains k

theorem remaining_iff {q : Nat} {keys prior : List Nat} :
    q ∈ remaining keys prior ↔ q ∈ prior ∧ q ∉ keys := by
  simp [remaining,List.contains_iff_mem]

/-- Structural subtraction rather than producer masking. Removing a
wrapper preserves its record shell and keeps existing payload states. -/
def delete (keys : List Nat) : Ty Row → Ty Row
  | .union a b => .union (delete keys a) (delete keys b)
  | .inter a b => .inter (delete keys a) (delete keys b)
  | .mask hs a => .mask (remaining keys hs) (delete keys a)
  | .record k p a => if k ∈ keys then shell (delete keys a) else .record k p (delete keys a)
  | .recordDefault k a p =>
    if k ∈ keys then shell (delete keys a) else .recordDefault k (delete keys a) p
  | t => t

def Query (keys : List Nat) (labels : List Nat) (q q' : Nat) : Prop :=
  (q ∈ keys → q' ∉ keys ∧ q' ∉ labels) ∧ (q ∉ keys → q'=q)

theorem query_sub {keys labels q q'} (atRoot : Query keys labels q q') (contained : xs ⊆ labels) :
    Query keys xs q q' :=
  ⟨fun active => ⟨(atRoot.1 active).1,fun here => (atRoot.1 active).2 (contained here)⟩,atRoot.2⟩

theorem query_nonremoved (link : Query keys seen q q') : q' ∉ keys := by
  by_cases is : q ∈ keys
  · exact (link.1 is).1
  · rw [link.2 is]; exact is

theorem query_other {q q' k : Nat} {keys labels newer older : List Nat} (link : Query keys labels q q')
    (exposed : k ∈ labels) (kept : k ∉ keys) (masked : q ∈ newer ↔ q' ∈ older) :
    (q = k ∧ k ∉ newer) ↔ (q' = k ∧ k ∉ older) := by
  by_cases active : q ∈ keys
  · have noNew : q ≠ k := fun e => kept (e ▸ active)
    have noOld : q' ≠ k := fun e => (link.1 active).2 (e.symm ▸ exposed)
    simp [noNew,noOld]
  · have sameQ := link.2 active
    subst q'
    by_cases same : q=k
    · subst k
      exact and_congr Iff.rfl (not_congr masked)
    · simp [same]

theorem query_mask {q q' : Nat} {keys labels newer older hs : List Nat} (link : Query keys labels q q')
    (has : ∀ k ∈ hs, k ∈ labels)
    (masked : q ∈ newer ↔ q' ∈ older) :
    q ∈ newer ++ remaining keys hs ↔ q' ∈ older ++ hs := by
  simp only [List.mem_append,remaining_iff]
  by_cases active : q ∈ keys
  · have gone : q' ∉ hs := fun h => (link.1 active).2 (has _ h)
    simp [active,gone,masked]
  · rw [link.2 active] at masked ⊢
    simp [active,masked]

/-- Unconsumed fields keep their original query. A consumed field
takes the exact absent-label behavior of one truly absent query. -/
theorem fields (keys : List Nat) (t : Ty Row) (q q' : Nat) (newer older : List Nat)
    (link : Query keys (outerLabels t) q q') (masked : q ∈ newer ↔ q' ∈ older) :
    ∀ o : Observation Row,
      (requiredField (leRow := leRow) (env := env) (ordered := order) newer (delete keys t) q o ↔
        requiredField (leRow := leRow) (env := env) (ordered := order) older t q' o) ∧
      (optionalField (leRow := leRow) (env := env) (ordered := order) newer (delete keys t) q o ↔
        optionalField (leRow := leRow) (env := env) (ordered := order) older t q' o) := by
  induction t using CommonNominalFinite.Ty.rec (motive_2 := fun _ => True)
    (motive_3 := fun _ => True) generalizing newer older with
  | union a b ia ib =>
    intro o
    have l := ia newer older (query_sub link (fun _ h => List.mem_append_left _ h)) masked o
    have r := ib newer older (query_sub link (fun _ h => List.mem_append_right _ h)) masked o
    simp only [requiredField,optionalField,delete,MaskedProbeStep] at l r ⊢
    exact ⟨and_congr l.1 r.1,and_congr l.2 r.2⟩
  | inter a b ia ib =>
    intro o
    have l := ia newer older (query_sub link (fun _ h => List.mem_append_left _ h)) masked o
    have r := ib newer older (query_sub link (fun _ h => List.mem_append_right _ h)) masked o
    simp only [requiredField,optionalField,delete,MaskedProbeStep] at l r ⊢
    exact ⟨or_congr l.1 r.1,or_congr l.2 r.2⟩
  | mask hs a ih =>
    intro o
    exact ih (newer ++ remaining keys hs) (older ++ hs)
      (query_sub link (fun _ h => List.mem_append_right _ h))
      (query_mask link (fun _ h => List.mem_append_left _ h) masked) o
  | record k payload a _ ih =>
    intro o
    have pair := ih newer older (query_sub link (fun _ h => List.mem_cons_of_mem _ h)) masked o
    by_cases removed : k ∈ keys
    · have no : q' ≠ k := fun h => query_nonremoved link (h ▸ removed)
      rw [delete,ite_eq_left removed]
      refine ⟨(required_eq _ _ _ _).trans ?_,(optional_eq _ _ _ _).trans ?_⟩
      · simpa only [requiredField,MaskedProbeStep,no,false_and,ite_false] using pair.1
      · simp only [optionalField,MaskedProbeStep,no,false_and,ite_false] at pair ⊢
        exact or_congr pair.2 Iff.rfl
    · have shapes := query_other link List.mem_cons_self removed masked
      rw [delete,ite_eq_right removed]
      unfold requiredField optionalField at pair ⊢
      simp only [MaskedProbeStep]
      by_cases same : q = k ∧ k ∉ newer
      · have atOld := shapes.mp same
        simp [same,atOld]
      · have atOld : ¬(q' = k ∧ k ∉ older) := fun h => same (shapes.mpr h)
        simpa only [same,atOld,ite_false] using ⟨pair.1,or_congr pair.2 Iff.rfl⟩
  | recordDefault k a payload ih _ =>
    intro o
    have rel := query_sub link (fun _ h => List.mem_cons_of_mem _ h)
    have pair := ih newer older rel masked o
    by_cases removed : k ∈ keys
    · have no : q' ≠ k := fun h => query_nonremoved link (h ▸ removed)
      rw [delete,ite_eq_left removed]
      refine ⟨(required_eq _ _ _ _).trans ?_,(optional_eq _ _ _ _).trans ?_⟩
      · simpa only [requiredField,MaskedProbeStep,no,false_and,ite_false] using pair.1
      · simp only [optionalField,MaskedProbeStep,no,false_and,ite_false] at pair ⊢
        exact or_congr pair.2 Iff.rfl
    · have shapes := query_other link List.mem_cons_self removed masked
      have inhabits := (ih newer older rel masked .trivial).1
      rw [delete,ite_eq_right removed]
      unfold requiredField at inhabits
      unfold requiredField optionalField at pair ⊢
      simp only [MaskedProbeStep]
      by_cases same : q = k ∧ k ∉ newer
      · have atOld := shapes.mp same
        have base : MaskedProbeStep leRow env order [] payload o ↔ MaskedProbeStep leRow env order [] payload o := Iff.rfl
        have composed := and_congr pair.2 (or_congr inhabits base)
        rw [ite_eq_left same,ite_eq_left atOld,ite_eq_left same,ite_eq_left atOld]
        exact ⟨composed,or_congr composed Iff.rfl⟩
      · have atOld : ¬(q' = k ∧ k ∉ older) := fun h => same (shapes.mpr h)
        simpa only [same,atOld,ite_false] using ⟨pair.1,or_congr pair.2 Iff.rfl⟩
  | exactEmpty =>
    intro o
    simp [delete,requiredField,optionalField,MaskedProbeStep,masked]
  | _ =>
    first | (intro o; exact ⟨Iff.rfl,Iff.rfl⟩) | trivial

end Yulang.GeneralDeclarativeExactDeleteFinite337
