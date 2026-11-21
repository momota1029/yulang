import Yulang.GeneralDeclarativeTraceNames321
import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
namespace Yulang.GeneralDeclarativeFootprint321
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeTraceNames321 (names namesMany)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (TyTerm RowTerm)
open CommonNominalFullCarrier (model)

def rowSources : Core.PresenceGeneration.RowTerm Nat → List Nat
  | .var name => [name]
  | .empty => []
  | .join first last => rowSources first ++ rowSources last

def typeSources : Core.PresenceGeneration.TyTerm Nat → List Nat
  | .var name => [name]
  | .union first last | .inter first last | .pair first last | .record _ first last |
      .recordDefault _ first last => typeSources first ++ typeSources last
  | .required _ child | .variant _ child => typeSources child
  | .arrow first incoming last outgoing =>
      typeSources first ++ rowSources incoming ++ typeSources last ++ rowSources outgoing
  | _ => []

def atomSources : PresenceNormalForm.Atom Nat → List Nat
  | .tyLe first last => typeSources first ++ typeSources last
  | .rowLe first last => rowSources first ++ rowSources last

section
variable {first last : Assignment}

theorem row_eval_same (term : RowTerm Nat)
    (same : ∀ name ∈ rowSources term, first name = last name) :
    term.eval model first = term.eval model last := by
  induction term with
  | var name => simp only [RowTerm.eval,same name (by simp [rowSources])]
  | empty => rfl
  | join left right ih₁ ih₂ =>
    simp only [RowTerm.eval,ih₁ (fun n h => same n (List.mem_append_left _ h)),
      ih₂ (fun n h => same n (List.mem_append_right _ h))]

theorem type_eval_same (term : TyTerm Nat)
    (same : ∀ name ∈ typeSources term, first name = last name) :
    term.eval model first = term.eval model last := by
  induction term with
  | var name => simp only [TyTerm.eval,same name (by simp [typeSources])]
  | base | bottom | top | emptyRecord | exactEmpty => rfl
  | required label child ih | variant label child ih =>
    simp only [TyTerm.eval,ih same]
  | union a b ia ib | inter a b ia ib | pair a b ia ib =>
    simp only [TyTerm.eval,ia (fun n h => same n (List.mem_append_left _ h)),
      ib (fun n h => same n (List.mem_append_right _ h))]
  | record label a b ia ib | recordDefault label a b ia ib =>
    simp only [TyTerm.eval,ia (fun n h => same n (List.mem_append_left _ h)),
      ib (fun n h => same n (List.mem_append_right _ h))]
  | arrow a incoming b outgoing ia ib =>
    have one := ia (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inl (Or.inl (Or.inl h))))
    have two := row_eval_same incoming (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inl (Or.inl (Or.inr h))))
    have three := ib (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inl (Or.inr h)))
    have four := row_eval_same outgoing (fun n h => same n (by simp only [typeSources,List.mem_append]; exact Or.inr h))
    simp only [TyTerm.eval,one,two,three,four]

theorem atom_same (atom : PresenceNormalForm.Atom Nat)
    (same : ∀ name ∈ atomSources atom, first name = last name) :
    atom.Holds model first ↔ atom.Holds model last := by
  cases atom with
  | tyLe a b =>
    simp only [PresenceNormalForm.Atom.Holds,type_eval_same a (fun n h => same n (List.mem_append_left _ h)),
      type_eval_same b (fun n h => same n (List.mem_append_right _ h))]
  | rowLe a b =>
    simp only [PresenceNormalForm.Atom.Holds,row_eval_same a (fun n h => same n (List.mem_append_left _ h)),
      row_eval_same b (fun n h => same n (List.mem_append_right _ h))]

end

def equationNames (eqn : Equation) : List Nat := eqn.left :: names eqn.right

def stateNames (s : State) : List Nat :=
  (s.normal.ordinary.flatMap atomSources ++ s.normal.intervals.flatMap (fun pr => [pr.1,pr.2])) ++
    s.equations.flatMap equationNames

mutual
 theorem value_same (first last : Assignment) (mode) (exp : Expr)
    (same : ∀ n ∈ names exp, first n = last n) :
    value (environment first) mode exp = value (environment last) mode exp := by
  cases exp with
  | «variable» n =>
    have equal := same n List.mem_cons_self
    simp only [value,environment,equal]
  | primitive tag args =>
    simp only [value,values_same first last mode args same]
  | nominal tag args =>
    simp only [value,values_same first last .actual args same]
  | record label x y | join x y =>
    simp only [value,value_same first last mode x (fun n h => same n (List.mem_append_left _ h)),
      value_same first last mode y (fun n h => same n (List.mem_append_right _ h))]
  | variant label x =>
    simp only [value,value_same first last mode x same]
 termination_by sizeOf exp

 theorem values_same (first last : Assignment) (mode) (es : List Expr)
    (same : ∀ n ∈ namesMany es, first n = last n) :
    values (environment first) mode es = values (environment last) mode es := by
  cases es with
  | nil => rfl
  | cons x xs =>
    simp only [values,value_same first last mode x (fun n h => same n (List.mem_append_left _ h)),
      values_same first last mode xs (fun n h => same n (List.mem_append_right _ h))]
 termination_by sizeOf es
end

theorem preserves_models (s : State) {first last : Assignment}
    (same : ∀ name ∈ stateNames s, first name = last name) : Models s first ↔ Models s last := by
  have normal (a) (present : a ∈ s.normal.ordinary) : a.Holds CommonNominalFullCarrier.model first ↔
      a.Holds CommonNominalFullCarrier.model last :=
    atom_same a (fun n used => same n (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨a,present,used⟩))))
  have spans (pr) (present : pr ∈ s.normal.intervals) :
      first pr.1 = last pr.1 ∧ first pr.2 = last pr.2 :=
    ⟨same _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨pr,present,List.mem_cons_self⟩))),same _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨pr,present,List.mem_cons_of_mem _ List.mem_cons_self⟩)))⟩
  have eqs (row) (present : row ∈ s.equations) : GeneralDeclarativeEntailment320.Holds first row ↔
      GeneralDeclarativeEntailment320.Holds last row := by
    have atName := same row.left (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨row,present,List.mem_cons_self⟩))
    have atExpr : ∀ n ∈ names row.right, first n = last n := fun n used =>
      same n (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨row,present,List.mem_cons_of_mem _ used⟩))
    simp only [GeneralDeclarativeEntailment320.Holds,atName,value_same first last .actual _ atExpr]
  constructor
  · intro valid
    refine ⟨⟨fun a h => (normal a h).mp (valid.1.1 a h),?_⟩,fun eq h => (eqs eq h).mp (valid.2 eq h)⟩
    intro pr there
    have span := valid.1.2 pr there
    rwa [(spans pr there).1,(spans pr there).2] at span
  · intro valid
    refine ⟨⟨fun a h => (normal a h).mpr (valid.1.1 a h),?_⟩,fun eq h => (eqs eq h).mpr (valid.2 eq h)⟩
    intro pr there
    rw [(spans pr there).1,(spans pr there).2]
    exact valid.1.2 pr there

end Yulang.GeneralDeclarativeFootprint321
