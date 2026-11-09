import Yulang.CommonRoleStructuralCarrierCoverage
import Yulang.CommonRoleSettledConstraints

/-! Preservation of the actual ordinary-state syntactic certificates under
supported finite structural closure. No new ordinary semantic rule is added. -/
namespace Yulang.CommonRoleStructuralStateGrammar
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom)
open CommonRoleStructuralCarrierCoverage (Derives)
open CommonRoleSettledConstraints (State)
open PresenceGeneratedChildGrammar (upper lower)
open PresenceGeneratedWidth (widthTail)
open PresenceSourceConstraintSupport (simpleTyRows simpleRow)

def Good (seeds : List (Atom (Fin n))) (x : Atom (Fin n)) : Prop :=
  PresenceGeneratedChildGrammar.GoodAtom x ∧
  PresenceSourceConstraintSupport.GoodAtom x ∧
  (∀ l r, x = .tyLe l r → ∀ tail, widthTail l = some tail →
    Derives seeds (.tyLe tail .emptyRecord))

theorem upper_width (seeds : List (Atom (Fin n))) (l r : TyTerm (Fin n))
    (h : upper l = true) :
    ∀ a b, Atom.tyLe l r = .tyLe a b → ∀ tail,
      widthTail a = some tail → Derives seeds (.tyLe tail .emptyRecord) := by
  intro a b eq tail ht
  cases eq
  rw [PresenceGeneratedWidth.upper_no_width l h] at ht
  cases ht

theorem expand_good (seeds : List (Atom (Fin n))) (k : Nat) (l r : TyTerm (Fin n))
    (h : Good seeds (.tyLe l r)) :
    ∀ x ∈ CommonRoleStructuralDecomposition.expandFuel k l r, Good seeds x := by
  induction k generalizing l r with
  | zero => simpa [CommonRoleStructuralDecomposition.expandFuel] using h
  | succ k ih =>
    simp only [CommonRoleStructuralDecomposition.expandFuel]
    split
    · rename_i a b c d
      have hh := h
      simp only [Good, PresenceGeneratedChildGrammar.GoodAtom, lower, upper,
        PresenceSourceConstraintSupport.GoodAtom, simpleTyRows, Bool.and_eq_true] at hh
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ih a c ⟨⟨PresenceGeneratedChildGrammar.upper_lower _ hh.1.1.1,hh.1.2.1⟩,
          ⟨hh.2.1.1.1,hh.2.1.2.1⟩,upper_width seeds a c hh.1.1.1⟩ x hx
      · exact ih b d ⟨⟨PresenceGeneratedChildGrammar.upper_lower _ hh.1.1.2,hh.1.2.2⟩,
          ⟨hh.2.1.1.2,hh.2.1.2.2⟩,upper_width seeds b d hh.1.1.2⟩ x hx
    · rename_i a ea b eb c ec d ed
      have hh := h
      simp only [Good, PresenceGeneratedChildGrammar.GoodAtom, lower, upper,
        PresenceSourceConstraintSupport.GoodAtom, simpleTyRows, Bool.and_eq_true] at hh
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with ((hx | rfl) | hx) | rfl
      · exact ih c a ⟨⟨PresenceGeneratedChildGrammar.upper_lower _ hh.1.2.1,hh.1.1.1⟩,
          ⟨hh.2.1.2.1.1.1,hh.2.1.1.1.1.1⟩,upper_width seeds c a hh.1.2.1⟩ x hx
      · exact ⟨trivial,hh.2.1.1.1.1.2,by intros; contradiction⟩
      · exact ih b d ⟨⟨PresenceGeneratedChildGrammar.upper_lower _ hh.1.1.2,hh.1.2.2⟩,
          ⟨hh.2.1.1.1.2,hh.2.1.2.1.2⟩,upper_width seeds b d hh.1.1.2⟩ x hx
      · exact ⟨trivial,hh.2.1.2.2,by intros; contradiction⟩
    · rename_i i a j b
      have impossible : upper (.variant j b : TyTerm (Fin n)) = true := h.1.2
      cases impossible
    · simpa using h

theorem derived_good (s : State n) (x : Atom (Fin n)) (h : Derives s.atoms x) :
    Good s.atoms x := by
  induction h with
  | seed a ha =>
    refine ⟨s.child a ha,s.rows a ha,?_⟩
    intro l r eq tail ht
    subst a
    exact .seed _ (s.width l r ha tail ht)
  | split a b _ hb ih =>
    cases a with
    | tyLe l r => exact expand_good s.atoms _ l r ih b hb
    | rowLe l r => simpa [CommonRoleStructuralDecomposition.atom] using (List.mem_singleton.mp hb ▸ ih)
  | trans a b c ha hb hc iha ihb =>
    cases a <;> cases b <;> simp only [CommonRoleFiniteStructuralClosure.compose] at hc
    case tyLe.tyLe l m m' r =>
      split at hc
      · have eq : c = .tyLe l r := by simpa using hc
        subst c
        exact ⟨⟨iha.1.1,ihb.1.2⟩,⟨iha.2.1.1,ihb.2.1.2⟩,
          fun a b eq tail ht => by cases eq; exact iha.2.2 l m rfl tail ht⟩
      · simp at hc
    all_goals simp at hc

def normalize (s : State n) : State n where
  atoms := CommonRoleFiniteStructuralClosure.normalize s.atoms
  child := fun x hx => (derived_good s x ((CommonRoleStructuralCarrierCoverage.normalize_membership s.atoms x).mp hx)).1
  rows := fun x hx => (derived_good s x ((CommonRoleStructuralCarrierCoverage.normalize_membership s.atoms x).mp hx)).2.1
  width := by
    intro l r hx tail ht
    apply (CommonRoleStructuralCarrierCoverage.normalize_membership s.atoms _).mpr
    exact (derived_good s _ ((CommonRoleStructuralCarrierCoverage.normalize_membership s.atoms _).mp hx)).2.2 l r rfl tail ht
end Yulang.CommonRoleStructuralStateGrammar
