import Yulang.ConstraintNormalForm
import Yulang.TypeConstraintGraph
import Yulang.RowFlowSchemes

/-!
# Paired type and row problems from the original source formulas

Splitting a finite clause separates its two kinds of inequalities while
retaining the same slot indices. In particular, the row of a computation is
not replaced by a fresh independent row during this transformation.

The final theorem relates the original source judgment to these computed
problems, including subsumption at the result. No solver or successful
assignment is assumed here; a solver can consume the two finite lists.
-/

namespace Yulang.ConstraintProblems

open Inference ConstraintNormalForm

variable {n : Nat}

structure Problem (n : Nat) where
  types : TypeConstraintGraph.Problem n
  rows : RowFlowSchemes.Problem n

def split : List (Atom (Fin n)) → Problem n
  | [] => ⟨[], []⟩
  | .tyLe left right :: rest =>
      let result := split rest
      ⟨(left, right) :: result.types, result.rows⟩
  | .rowLe left right :: rest =>
      let result := split rest
      ⟨result.types, (left, right) :: result.rows⟩

def RowHolds (model : Model) (rows : Fin n → model.Row)
    (constraints : RowFlowSchemes.Problem n) : Prop :=
  ∀ constraint ∈ constraints,
    model.subRow (TypeConstraintGraph.rowEval model.empty model.join rows constraint.1)
      (TypeConstraintGraph.rowEval model.empty model.join rows constraint.2)

def Problem.Holds (model : Model) (problem : Problem n)
    (values : Fin n → model.Ty) (rows : Fin n → model.Row) : Prop :=
  TypeConstraintGraph.Holds model rows values problem.types ∧ RowHolds model rows problem.rows

@[simp] theorem rowHolds_nil (model : Model) (rows : Fin n → model.Row) :
    RowHolds model rows [] := by
  intro constraint impossible
  cases impossible

@[simp] theorem rowHolds_cons (model : Model) (rows : Fin n → model.Row)
    (constraint : RowTerm (Fin n) × RowTerm (Fin n)) (rest : RowFlowSchemes.Problem n) :
    RowHolds model rows (constraint :: rest) ↔
      model.subRow (TypeConstraintGraph.rowEval model.empty model.join rows constraint.1)
        (TypeConstraintGraph.rowEval model.empty model.join rows constraint.2) ∧
        RowHolds model rows rest := by
  simp only [RowHolds, List.mem_cons, forall_eq_or_imp]

/-- Both lists use the same finite slots as the original clause. -/
theorem split_exact (model : Model) (atoms : List (Atom (Fin n)))
    (values : Fin n → model.Ty) (rows : Fin n → model.Row) :
    (split atoms).Holds model values rows ↔ All model (fun i => (values i, rows i)) atoms := by
  induction atoms with
  | nil => simp [split, Problem.Holds]
  | cons atom rest ih =>
      cases atom with
      | tyLe left right =>
          simpa only [split, Problem.Holds, TypeConstraintGraph.holds_cons, All,
            List.mem_cons, forall_eq_or_imp, Atom.Holds, TypeConstraintGraph.evaluate,
            and_assoc] using and_congr_right (fun _ => ih)
      | rowLe left right =>
          simp only [split, Problem.Holds, rowHolds_cons, All, List.mem_cons,
            forall_eq_or_imp, Atom.Holds,
            TypeConstraintGraph.rowEval_eq model rows values left,
            TypeConstraintGraph.rowEval_eq model rows values right]
          constructor
          · rintro ⟨types, row, remainder⟩
            exact ⟨row, ih.mp ⟨types, remainder⟩⟩
          · rintro ⟨row, remainder⟩
            obtain ⟨types, remainder⟩ := ih.mpr remainder
            exact ⟨types, row, remainder⟩

theorem rowEval_flow (algebra : RowFlowSchemes.Algebra Row)
    (rows : Fin n → Row) (term : RowTerm (Fin n)) :
    TypeConstraintGraph.rowEval algebra.empty algebra.join rows term =
      RowFlowSchemes.eval algebra rows term := by
  induction term <;> simp_all [TypeConstraintGraph.rowEval, RowFlowSchemes.eval]

theorem rowHolds_flow (model : Model) (algebra : RowFlowSchemes.Algebra model.Row)
    (empty : algebra.empty = model.empty)
    (join : algebra.join = model.join) (le : algebra.le = model.subRow)
    (rows : Fin n → model.Row) (constraints : RowFlowSchemes.Problem n) :
    RowHolds model rows constraints ↔ RowFlowSchemes.Models algebra constraints rows := by
  simp only [RowHolds, RowFlowSchemes.Models, RowFlowSchemes.Constraint.Holds,
    ← empty, ← join, ← le, rowEval_flow]

section Subsumption

variable (model : Model)
  (tyTrans : ∀ {a b c}, model.subTy a b → model.subTy b c → model.subTy a c)
  (rowRefl : ∀ row, model.subRow row row)
  (rowTrans : ∀ {a b c}, model.subRow a b → model.subRow b c → model.subRow a c)

include tyTrans rowTrans

private theorem comp_trans {a b c : Comp model} (left : Comp.le model a b)
    (right : Comp.le model b c) : Comp.le model a c :=
  ⟨tyTrans left.1 right.1, rowTrans left.2 right.2⟩

include rowRefl

/-- Subsumption is admissible for the original judgment, including captured
polymorphic bindings. Its only model assumptions are preorder laws. -/
theorem typing_subsumption {bindings : List (Binding model)} {expression : Expr}
    {source target : Comp model} (derivation : Typing model bindings expression source)
    (upper : Comp.le model source target) : Typing model bindings expression target := by
  revert target
  induction derivation using Typing.rec
    (motive_2 := fun binding source _ => ∀ target, Comp.le model source target →
      BindingTyping model binding target) with
  | var lookup _ ih =>
      intro target upper
      exact .var lookup (ih target upper)
  | lit bounded =>
      intro _ upper
      exact .lit (comp_trans model tyTrans rowTrans bounded upper)
  | lam body bounded _ =>
      intro _ upper
      exact .lam body (comp_trans model tyTrans rowTrans bounded upper)
  | app function argument bounded _ _ =>
      intro _ upper
      exact .app function argument (comp_trans model tyTrans rowTrans bounded upper)
  | letValue value defined _ _ ih =>
      intro _ upper
      exact .letValue value defined (ih upper)
  | letComputed defined body bounded _ _ =>
      intro _ upper
      exact .letComputed defined body (comp_trans model tyTrans rowTrans bounded upper)
  | branch condition yes no bounded _ _ _ =>
      intro _ upper
      exact .branch condition yes no (comp_trans model tyTrans rowTrans bounded upper)
  | pair left right bounded _ _ =>
      intro _ upper
      exact .pair left right (comp_trans model tyTrans rowTrans bounded upper)
  | fst pair bounded _ =>
      intro _ upper
      exact .fst pair (comp_trans model tyTrans rowTrans bounded upper)
  | snd pair bounded _ =>
      intro _ upper
      exact .snd pair (comp_trans model tyTrans rowTrans bounded upper)
  | emptyRecord bounded =>
      intro _ upper
      exact .emptyRecord (comp_trans model tyTrans rowTrans bounded upper)
  | record value rest recordType bounded _ _ =>
      intro _ upper
      exact .record value rest recordType (comp_trans model tyTrans rowTrans bounded upper)
  | field record bounded _ =>
      intro _ upper
      exact .field record (comp_trans model tyTrans rowTrans bounded upper)
  | variant value bounded _ =>
      intro _ upper
      exact .variant value (comp_trans model tyTrans rowTrans bounded upper)
  | mono bounded _ upper =>
      exact .mono (comp_trans model tyTrans rowTrans bounded upper)
  | poly _ row ih _ upper =>
      exact .poly (ih ⟨upper.1, rowRefl model.empty⟩)
        (rowTrans row upper.2)
  | signature bounded _ upper =>
      exact .signature (comp_trans model tyTrans rowTrans bounded upper)

theorem binding_subsumption {binding : Binding model} {source target : Comp model}
    (derivation : BindingTyping model binding source) (upper : Comp.le model source target) :
    BindingTyping model binding target := by
  cases derivation with
  | mono bounded => exact .mono (comp_trans model tyTrans rowTrans bounded upper)
  | poly value row =>
      exact .poly (typing_subsumption model tyTrans rowRefl rowTrans value
        ⟨upper.1, rowRefl model.empty⟩) (rowTrans row upper.2)
  | signature bounded => exact .signature (comp_trans model tyTrans rowTrans bounded upper)

end Subsumption

/-- An output instance of the original paired constraints. The comparison at
the output is ordinary computation subsumption, not an additional constraint
on free parameters of a subsequently constructed scheme. -/
def Problem.Instance (model : Model) (problem : Problem n) (output : Fin n)
    (target : Comp model) : Prop :=
  ∃ values rows, problem.Holds model values rows ∧
    Comp.le model (values output, rows output) target

theorem closed_source_problems_exact (model : Model)
    (tyRefl : ∀ type, model.subTy type type)
    (tyTrans : ∀ {a b c}, model.subTy a b → model.subTy b c → model.subTy a c)
    (rowRefl : ∀ row, model.subRow row row)
    (rowTrans : ∀ {a b c}, model.subRow a b → model.subRow b c → model.subRow a c)
    (expression : Expr) (target : Comp model) :
    Typing model [] expression target ↔
      ∃ clause ∈ normalise (principal ([] : SchemeEnv Empty) expression),
        (split clause.pack).Instance model (Fin.last clause.locals) target := by
  constructor
  · intro typed
    obtain ⟨clause, member, assignment, result, held⟩ :=
      (closed_source_exact model expression target).mp typed
    refine ⟨clause, member, (fun i => (assignment i).1), (fun i => (assignment i).2),
      (split_exact model clause.pack _ _).mpr held, ?_⟩
    change Comp.le model (assignment (Fin.last clause.locals)) target
    rw [result]
    exact ⟨tyRefl _, rowRefl _⟩
  · rintro ⟨clause, member, values, rows, held, upper⟩
    have typed : Typing model [] expression (values (Fin.last clause.locals),
        rows (Fin.last clause.locals)) :=
      (closed_source_exact model expression _).mpr
        ⟨clause, member, (fun i => (values i, rows i)), rfl,
          (split_exact model clause.pack values rows).mp held⟩
    exact typing_subsumption model tyTrans rowRefl rowTrans typed upper

end Yulang.ConstraintProblems
