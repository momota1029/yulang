import Yulang.CommonCanonicalRowSyntax

/-!
# Finite row equations expressed by finite public type syntax

An intersection test is compiled to a union of ordinary arrows. No row-meet
constructor or residual parameter constraint is added to the interface.
-/

namespace Yulang.CommonCanonicalRowTests

open CommonCanonicalRowSyntax
open CommonCanonicalRowConstraints

def rowForm (row : Row scopes parameters) : Form scopes parameters :=
  .arrow .unit row .unit .empty

def lockForm (form : Form scopes parameters) : Form scopes parameters :=
  .arrow form .empty form .empty

def meetForm (first : Row scopes parameters) : List (Row scopes parameters) → Form scopes parameters
  | [] => rowForm first
  | next :: rest => .union (rowForm next) (meetForm first rest)

def meetEval (parameters : Fin count → Common.Row) (first : Row scopes count) :
    List (Row scopes count) → Common.Row
  | [] => rowEval parameters first
  | next :: rest => meetRow (rowEval parameters next) (meetEval parameters first rest)

/-- Every nonempty finite row intersection is represented by ordinary
type syntax, with every repeated row parameter shared exactly. -/
theorem meetForm_exact (first : Row scopes count) (rest : List (Row scopes count))
    (parameters : Fin count → Common.Row) :
    Common.Equivalent ((meetForm first rest).eval parameters)
      (rowType (meetEval parameters first rest)) := by
  induction rest with
  | nil => exact Common.equivalent_refl _
  | cons next rest ih =>
      exact Common.equivalent_trans
        (CommonCanonicalShapes.union_congr (Common.equivalent_refl _) ih)
        (arrow_union_input_rows (.base .unit) (.base .unit)
          (rowEval parameters next) (meetEval parameters first rest) Common.rowEmpty)

structure Test (scopes parameters : Nat) where
  first : Row scopes parameters
  rest : List (Row scopes parameters)
  expected : Row scopes 0

def Test.value (test : Test scopes parameters) : Form scopes parameters :=
  lockForm (meetForm test.first test.rest)

def Test.fixed (test : Test scopes parameters) : Form scopes 0 :=
  lockForm (rowForm test.expected)

def Test.Holds (test : Test scopes parameters) (assignment : Fin parameters → Common.Row) : Prop :=
  meetEval assignment test.first test.rest = rowEval Fin.elim0 test.expected

/-- An equation between a nonempty row intersection and a closed finite row
expression is exactly one ordinary subtype comparison. -/
theorem test_exact (test : Test scopes parameters) (assignment : Fin parameters → Common.Row) :
    Common.Subtype (test.value.eval assignment) (test.fixed.eval Fin.elim0) ↔ test.Holds assignment := by
  change Common.Subtype (lock ((meetForm test.first test.rest).eval assignment))
    (lock (rowType (rowEval Fin.elim0 test.expected))) ↔ _
  rw [lock_subtype_iff]
  have same := meetForm_exact test.first test.rest assignment
  constructor
  · intro below
    exact (locked_rows_subtype_iff _ _).mp ((lock_subtype_iff _ _).mpr
      (Common.equivalent_trans (Common.equivalent_symm same) below))
  · intro satisfied
    change meetEval assignment test.first test.rest = rowEval Fin.elim0 test.expected at satisfied
    rw [← satisfied]
    exact same

def problemValue : List (Test scopes parameters) → Form scopes parameters
  | [] => .unit
  | test :: rest => .pair test.value (problemValue rest)

def problemFixed : List (Test scopes parameters) → Form scopes 0
  | [] => .unit
  | test :: rest => .pair test.fixed (problemFixed rest)

def ProblemHolds (problem : List (Test scopes parameters)) (assignment : Fin parameters → Common.Row) : Prop :=
  ∀ test ∈ problem, test.Holds assignment

/-- A finite list of row equations is represented by a finite pair tuple.
The same row assignment enters every component. -/
theorem problem_exact (problem : List (Test scopes parameters))
    (assignment : Fin parameters → Common.Row) :
    Common.Subtype ((problemValue problem).eval assignment) ((problemFixed problem).eval Fin.elim0) ↔
      ProblemHolds problem assignment := by
  induction problem with
  | nil =>
      exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),
        fun _ => Common.subtype_refl _⟩
  | cons test rest ih =>
      have pair := Common.common_pair_iff (test.value.eval assignment)
        ((problemValue rest).eval assignment) (test.fixed.eval Fin.elim0)
        ((problemFixed rest).eval Fin.elim0)
      simp only [Common.model] at pair
      change Common.Subtype
        (Common.pair (test.value.eval assignment) ((problemValue rest).eval assignment))
        (Common.pair (test.fixed.eval Fin.elim0) ((problemFixed rest).eval Fin.elim0)) ↔ _
      rw [pair, test_exact, ih]
      simp only [ProblemHolds, List.mem_cons, forall_eq_or_imp]

def fixedInterface (problem : List (Test scopes parameters)) : Interface :=
  ⟨scopes, 0, problemFixed problem⟩

def familyInterface (problem : List (Test scopes parameters)) : Interface :=
  ⟨scopes, parameters,
    .union ((problemFixed problem).rename Fin.elim0) (problemValue problem)⟩

/-- Satisfiability is encoded by equality of the original public-instance
judgments of two finite symbolic interfaces. The first has zero generalized
slots; the second has exactly the original row-parameter count. -/
theorem problem_interfaces_exact (problem : List (Test scopes parameters)) :
    (∀ theory : RoleConstraints.Theory model, ∀ target : Inference.Comp model,
      QualifiedInference.BindingTyping model theory (fixedInterface problem).binding target ↔
      QualifiedInference.BindingTyping model theory (familyInterface problem).binding target) ↔
    ∃ assignment : Fin parameters → Common.Row, ProblemHolds problem assignment := by
  have emptyRows (assignment : Fin 0 → Common.Row) : assignment = Fin.elim0 := by
    funext index
    exact Fin.elim0 index
  have fixedMeaning (theory : RoleConstraints.Theory model) (target : Inference.Comp model) :
      QualifiedInference.BindingTyping model theory (fixedInterface problem).binding target ↔
        Common.Subtype ((problemFixed problem).eval Fin.elim0) target.1 := by
    rw [binding_instances_exact]
    constructor
    · rintro ⟨assignment, below⟩
      exact emptyRows assignment ▸ below
    · intro below
      exact ⟨Fin.elim0, below⟩
  have familyMeaning (theory : RoleConstraints.Theory model) (target : Inference.Comp model) :
      QualifiedInference.BindingTyping model theory (familyInterface problem).binding target ↔
        ∃ assignment : Fin parameters → Common.Row,
          Common.Subtype (.union ((problemFixed problem).eval Fin.elim0)
            ((problemValue problem).eval assignment)) target.1 := by
    rw [binding_instances_exact]
    change (∃ assignment : Fin parameters → Common.Row,
      Common.Subtype (.union (((problemFixed problem).rename Fin.elim0).eval assignment)
        ((problemValue problem).eval assignment)) target.1) ↔ _
    simp only [rename_eval, emptyRows]
  have semantic := family_equality_iff_satisfiable ((problemFixed problem).eval Fin.elim0)
    (fun assignment => (problemValue problem).eval assignment)
  constructor
  · intro same
    have families : ∀ type, Common.Subtype ((problemFixed problem).eval Fin.elim0) type ↔
        ∃ assignment : Fin parameters → Common.Row,
          Common.Subtype (.union ((problemFixed problem).eval Fin.elim0)
            ((problemValue problem).eval assignment)) type := by
      intro type
      exact (fixedMeaning (fun _ => True) (type, Common.rowEmpty)).symm.trans
        ((same (fun _ => True) (type, Common.rowEmpty)).trans
          (familyMeaning (fun _ => True) (type, Common.rowEmpty)))
    obtain ⟨assignment, below⟩ := semantic.mp families
    exact ⟨assignment, (problem_exact problem assignment).mp below⟩
  · rintro ⟨assignment, satisfied⟩ theory target
    have families := semantic.mpr ⟨assignment, (problem_exact problem assignment).mpr satisfied⟩
    exact (fixedMeaning theory target).trans
      ((families target.1).trans (familyMeaning theory target).symm)

end Yulang.CommonCanonicalRowTests
