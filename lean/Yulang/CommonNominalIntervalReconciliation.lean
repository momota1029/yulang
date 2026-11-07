import Yulang.CommonInvariantIntervals
import Yulang.CommonNominalHeads

/-!
# Finite reconciliation of dedicated nominal argument intervals

Descriptions retain a nominal ID and ordered type/row argument bounds.
They contain no centre. Independent models use the existing nominal Head
metadata and existing Common types/rows; no new semantic carrier/order is
introduced. This is reconciliation of one shared actual head, not a rule
merging separate branch values and not the complete source declaration solver.
-/

namespace Yulang.CommonNominalIntervalReconciliation

abbrev ArgumentBounds := CommonInvariantIntervals.Interval ⊕ (Common.Row × Common.Row)
abbrev Description := Nat × List ArgumentBounds
abbrev Argument := CommonNominalHeads.Argument
abbrev Head := CommonNominalHeads.Head

def rowHolds (bounds : Common.Row × Common.Row) (actual : Common.Row) : Prop :=
  Common.rowLe bounds.1 actual ∧ Common.rowLe actual bounds.2

def rowMerge (first last : Common.Row × Common.Row) : Common.Row × Common.Row :=
  (Common.rowJoin first.1 last.1, fun occurrence => first.2 occurrence ∧ last.2 occurrence)

theorem row_merge_exact (first last : Common.Row × Common.Row) (actual : Common.Row) :
    rowHolds (rowMerge first last) actual ↔ rowHolds first actual ∧ rowHolds last actual := by
  constructor
  · rintro ⟨lower, upper⟩
    have split := (Common.rowJoin_le_iff _ _ _).mp lower
    exact ⟨⟨split.1, fun occurrence member => (upper occurrence member).1⟩,
      split.2, fun occurrence member => (upper occurrence member).2⟩
  · rintro ⟨⟨firstLower, firstUpper⟩, lastLower, lastUpper⟩
    exact ⟨(Common.rowJoin_le_iff _ _ _).mpr ⟨firstLower, lastLower⟩,
      fun occurrence member => ⟨firstUpper occurrence member, lastUpper occurrence member⟩⟩

def ArgumentHolds : ArgumentBounds → Argument → Prop
  | .inl bounds, .value actual => CommonInvariantIntervals.Holds bounds actual
  | .inr bounds, .row actual => rowHolds bounds actual
  | _, _ => False

def mergeArgument : ArgumentBounds → ArgumentBounds → Option ArgumentBounds
  | .inl first, .inl last => some (.inl (CommonInvariantIntervals.merge first last))
  | .inr first, .inr last => some (.inr (rowMerge first last))
  | _, _ => none

def ArgumentResultHolds (result : Option ArgumentBounds) (actual : Argument) : Prop :=
  match result with
  | none => False
  | some bounds => ArgumentHolds bounds actual

theorem argument_merge_exact (first last : ArgumentBounds) (actual : Argument) :
    ArgumentResultHolds (mergeArgument first last) actual ↔
      ArgumentHolds first actual ∧ ArgumentHolds last actual := by
  cases first <;> cases last <;> cases actual <;>
    simp [mergeArgument, ArgumentResultHolds, ArgumentHolds,
      CommonInvariantIntervals.holds_merge_exact, row_merge_exact]

def ArgumentsHolds : List ArgumentBounds → List Argument → Prop
  | [], [] => True
  | first :: rest, actual :: actualRest => ArgumentHolds first actual ∧ ArgumentsHolds rest actualRest
  | _, _ => False

def mergeArguments : List ArgumentBounds → List ArgumentBounds → Option (List ArgumentBounds)
  | [], [] => some []
  | first :: rest, last :: tail => do
      let argument ← mergeArgument first last
      let arguments ← mergeArguments rest tail
      return argument :: arguments
  | _, _ => none

def ArgumentsResultHolds (result : Option (List ArgumentBounds)) (actual : List Argument) : Prop :=
  match result with
  | none => False
  | some bounds => ArgumentsHolds bounds actual

theorem arguments_merge_exact (first last : List ArgumentBounds) (actual : List Argument) :
    ArgumentsResultHolds (mergeArguments first last) actual ↔
      ArgumentsHolds first actual ∧ ArgumentsHolds last actual := by
  induction first generalizing last actual with
  | nil => cases last <;> cases actual <;> simp [mergeArguments, ArgumentsResultHolds, ArgumentsHolds]
  | cons first rest ih =>
      cases last with
      | nil => cases actual <;> simp [mergeArguments, ArgumentsResultHolds, ArgumentsHolds]
      | cons last tail =>
          cases actual with
          | nil =>
              cases headResult : mergeArgument first last <;>
                cases tailResult : mergeArguments rest tail <;>
                simp [mergeArguments, headResult, tailResult, ArgumentsResultHolds, ArgumentsHolds]
          | cons actual actualRest =>
              have head := argument_merge_exact first last actual
              have tailFacts := ih tail actualRest
              cases headResult : mergeArgument first last <;>
                cases tailResult : mergeArguments rest tail <;>
                simp_all [mergeArguments, ArgumentResultHolds, ArgumentsResultHolds, ArgumentsHolds,
                  and_assoc, and_left_comm]

def Holds (description : Description) (actual : Head) : Prop :=
  description.1 = actual.name ∧ ArgumentsHolds description.2 actual.arguments

def merge (first last : Description) : Option Description :=
  if first.1 = last.1 then
    (mergeArguments first.2 last.2).map fun arguments => (first.1, arguments)
  else none

def ResultHolds (result : Option Description) (actual : Head) : Prop :=
  match result with
  | none => False
  | some description => Holds description actual

/-- All nominal IDs, all arities and arbitrary ordered Common type/row
bounds. Different IDs, arities or kinds are rejected by actual finite syntax
inspection. Every successful bound occurrence applies to the same actual. -/
theorem nominal_merge_models_exact (first last : Description) (actual : Head) :
    ResultHolds (merge first last) actual ↔ Holds first actual ∧ Holds last actual := by
  by_cases same : first.1 = last.1
  · have arguments := arguments_merge_exact first.2 last.2 actual.arguments
    cases found : mergeArguments first.2 last.2 <;>
      simp_all [merge, ResultHolds, Holds, ArgumentsResultHolds, and_assoc, and_left_comm]
  · simp only [merge, same, ↓reduceIte, ResultHolds, false_iff, Holds, not_and]
    rintro ⟨firstName, _⟩ lastName _
    exact same (firstName.trans lastName.symm)

theorem arguments_holds_length (bounds : List ArgumentBounds) (actual : List Argument)
    (model : ArgumentsHolds bounds actual) : bounds.length = actual.length := by
  induction bounds generalizing actual with
  | nil => cases actual <;> simp_all [ArgumentsHolds]
  | cons head rest ih =>
      cases actual with
      | nil => cases model
      | cons actual tail => exact congrArg Nat.succ (ih tail model.2)

def pointArgument : Argument → ArgumentBounds
  | .value actual => .inl (CommonInvariantIntervals.point actual)
  | .row actual => .inr (actual, actual)

theorem point_argument_holds_exact (first last : Argument) :
    ArgumentHolds (pointArgument first) last ↔ first.Equivalent last := by
  cases first <;> cases last <;>
    simp [ArgumentHolds, pointArgument, CommonInvariantIntervals.Holds, CommonInvariantIntervals.point,
      rowHolds, CommonNominalHeads.Argument.Equivalent, CommonNominalHeads.Argument.Le]

theorem point_arguments_holds_exact (first last : List Argument) :
    ArgumentsHolds (first.map pointArgument) last ↔ CommonNominalHeads.ArgumentsEquivalent first last := by
  induction first generalizing last with
  | nil => cases last <;> rfl
  | cons first rest ih =>
      cases last <;>
        simp [ArgumentsHolds, CommonNominalHeads.ArgumentsEquivalent, point_argument_holds_exact, ih]

def pointHead (actual : Head) : Description :=
  (actual.name, actual.arguments.map pointArgument)

/-- The former point-head invariance relation is exactly the collapsed
interval special case, not the definition of general interval invariance. -/
theorem point_head_holds_exact (first last : Head) :
    Holds (pointHead first) last ↔ first.name = last.name ∧
      first.arguments.length = last.arguments.length ∧
        ∀ (index : Nat) (a b : Argument), first.arguments[index]? = some a → last.arguments[index]? = some b → a.Equivalent b := by
  simp only [Holds, pointHead, point_arguments_holds_exact, CommonNominalHeads.argumentsEquivalent_iff]

end Yulang.CommonNominalIntervalReconciliation
