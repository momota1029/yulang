import Yulang.CommonDeclaredNominalInspection

/-!
# Open bounds in finite nested nominal endpoints

This is finite *description syntax* for an ordinary-subtyping decomposition,
not another semantic type carrier. Ordinary leaves retain the original
presence terms and slots. Nominal nodes retain their declaration identity,
ordered kinds, and, at invariant positions, both original endpoints.

`point` is the collapsed special case. `interval` never stores an actual
type or a representative. The decomposition below emits all four old/cross
conditions when two invariant descriptions constrain the same argument.
Covariant and contravariant positions have ordinary point arguments; open
bounds at those positions are outside this particular description grammar.

The relation parameter in the local algebraic lemma is only a mathematical
interpretation of emitted obligations. It is not an algorithm argument or a
subtyping oracle. The recursive compiler is in the following module.
-/

namespace Yulang.CommonRecursiveNominalIntervals

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry)
open CommonDeclaredNominalVariance (Variance)
open PresenceNormalForm (Atom All)

inductive Bounds (Term : Type) where
  | point : Term → Bounds Term
  | interval : Term → Term → Bounds Term

def Bounds.lower : Bounds Term → Term
  | .point term | .interval term _ => term

def Bounds.upper : Bounds Term → Term
  | .point term | .interval _ term => term

/-- Original consistency checks and both cross checks, with no centre. -/
def Bounds.checks (first last : Bounds Term) : List (Term × Term) :=
  [(first.lower, first.upper), (first.lower, last.upper),
    (last.lower, first.upper), (last.lower, last.upper)]

theorem Bounds.checks_exact (le : Term → Term → Prop) (first last : Bounds Term) :
    (∀ pair ∈ first.checks last, le pair.1 pair.2) ↔
      le first.lower first.upper ∧ le last.lower last.upper ∧
        le first.lower last.upper ∧ le last.lower first.upper := by
  simp only [checks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, d, b, c⟩,
    fun ⟨a, b, c, d⟩ => ⟨a, c, d, b⟩⟩

inductive Endpoint (α : Type) where
  | ordinary : TyTerm α → Endpoint α
  | nominal : Nat → List (Bounds (Endpoint α) ⊕ Bounds (RowTerm α)) → Endpoint α

abbrev Argument (α : Type) := Bounds (Endpoint α) ⊕ Bounds (RowTerm α)

def argumentKind : Argument α → Kind
  | .inl _ => .value
  | .inr _ => .row

/-- A value obligation may itself have nominal endpoints. A row obligation
already belongs to the ordinary presence machine. -/
inductive Obligation (α : Type) where
  | value : Endpoint α → Endpoint α → Obligation α
  | row : RowTerm α → RowTerm α → Obligation α

def valueChecks (first last : Bounds (Endpoint α)) : List (Obligation α) :=
  (first.checks last).map fun pair => .value pair.1 pair.2

def rowChecks (first last : Bounds (RowTerm α)) : List (Obligation α) :=
  (first.checks last).map fun pair => .row pair.1 pair.2

/-- The finite first step reads declaration metadata; it does not solve or
discard any endpoint obligation. -/
def decomposeArgument (parameter : Parameter) (first last : Argument α) :
    Option (List (Obligation α)) :=
  match parameter, first, last with
  | ⟨.value, .covariant⟩, .inl (.point a), .inl (.point b) => some [.value a b]
  | ⟨.value, .contravariant⟩, .inl (.point a), .inl (.point b) => some [.value b a]
  | ⟨.value, .invariant⟩, .inl a, .inl b => some (valueChecks a b)
  | ⟨.value, .unused⟩, .inl _, .inl _ => some []
  | ⟨.row, .covariant⟩, .inr (.point a), .inr (.point b) => some [.row a b]
  | ⟨.row, .contravariant⟩, .inr (.point a), .inr (.point b) => some [.row b a]
  | ⟨.row, .invariant⟩, .inr a, .inr b => some (rowChecks a b)
  | ⟨.row, .unused⟩, .inr _, .inr _ => some []
  | _, _, _ => none

def append (first last : Option (List β)) : Option (List β) := do
  let first ← first
  let last ← last
  return first ++ last

def decomposeArguments : Declaration → List (Argument α) → List (Argument α) →
    Option (List (Obligation α))
  | [], [], [] => some []
  | parameter :: rest, first :: tail, last :: suffix =>
      append (decomposeArgument parameter first last) (decomposeArguments rest tail suffix)
  | _, _, _ => none

def Obligation.Holds (le : Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) : Obligation α → Prop
  | .value first last => le first last
  | .row first last => Common.rowLe
      (first.eval Common.model assignment) (last.eval Common.model assignment)

def ResultHolds (meaning : β → Prop) (result : Option (List β)) : Prop :=
  ∃ items, result = some items ∧ ∀ item ∈ items, meaning item

@[simp] theorem result_none (meaning : β → Prop) : ¬ ResultHolds meaning none := by
  simp [ResultHolds]

@[simp] theorem result_some (meaning : β → Prop) (items : List β) :
    ResultHolds meaning (some items) ↔ ∀ item ∈ items, meaning item := by
  simp [ResultHolds]

theorem append_exact (meaning : β → Prop) (first last : Option (List β)) :
    ResultHolds meaning (append first last) ↔
      ResultHolds meaning first ∧ ResultHolds meaning last := by
  cases first <;> cases last <;>
    simp [append, List.mem_append, or_imp, forall_and]

/-- Independent rules for the argument's declared direction. Invariance
means joint open-bound consistency, not equality of chosen point arguments. -/
def ArgumentRel (le : Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) : Parameter → Argument α → Argument α → Prop
  | ⟨.value, .covariant⟩, .inl (.point a), .inl (.point b) => le a b
  | ⟨.value, .contravariant⟩, .inl (.point a), .inl (.point b) => le b a
  | ⟨.value, .invariant⟩, .inl a, .inl b =>
      le a.lower a.upper ∧ le b.lower b.upper ∧ le a.lower b.upper ∧ le b.lower a.upper
  | ⟨.value, .unused⟩, .inl _, .inl _ => True
  | ⟨.row, .covariant⟩, .inr (.point a), .inr (.point b) =>
      Common.rowLe (a.eval Common.model assignment) (b.eval Common.model assignment)
  | ⟨.row, .contravariant⟩, .inr (.point a), .inr (.point b) =>
      Common.rowLe (b.eval Common.model assignment) (a.eval Common.model assignment)
  | ⟨.row, .invariant⟩, .inr a, .inr b =>
      let rel := fun first last : RowTerm α => Common.rowLe
        (first.eval Common.model assignment) (last.eval Common.model assignment)
      rel a.lower a.upper ∧ rel b.lower b.upper ∧ rel a.lower b.upper ∧ rel b.lower a.upper
  | ⟨.row, .unused⟩, .inr _, .inr _ => True
  | _, _, _ => False

def ArgumentsRel (le : Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) :
    Declaration → List (Argument α) → List (Argument α) → Prop
  | [], [], [] => True
  | parameter :: rest, first :: tail, last :: suffix =>
      ArgumentRel le assignment parameter first last ∧ ArgumentsRel le assignment rest tail suffix
  | _, _, _ => False

theorem decompose_argument_exact (le : Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) (parameter : Parameter) (first last : Argument α) :
    ResultHolds (Obligation.Holds le assignment) (decomposeArgument parameter first last) ↔
      ArgumentRel le assignment parameter first last := by
  rcases parameter with ⟨kind, mode⟩
  cases first <;> cases last <;> rename_i first last
  all_goals cases first <;> cases last <;> cases kind <;> cases mode <;>
    simp [decomposeArgument, ArgumentRel, valueChecks, rowChecks,
      Obligation.Holds, Bounds.checks, Bounds.lower, Bounds.upper,
      and_assoc, and_left_comm, and_comm]

/-- All declared arities and ordered kinds are checked by the finite pass. -/
theorem decompose_arguments_exact (le : Endpoint α → Endpoint α → Prop)
    (assignment : α → Comp Common.model) (declaration : Declaration)
    (first last : List (Argument α)) :
    ResultHolds (Obligation.Holds le assignment) (decomposeArguments declaration first last) ↔
      ArgumentsRel le assignment declaration first last := by
  induction declaration generalizing first last with
  | nil => cases first <;> cases last <;> simp [decomposeArguments, ArgumentsRel]
  | cons parameter rest ih =>
      cases first with
      | nil => cases last <;> simp [decomposeArguments, ArgumentsRel]
      | cons first tail =>
          cases last with
          | nil => simp [decomposeArguments, ArgumentsRel]
          | cons last suffix =>
              simp only [decomposeArguments, append_exact, decompose_argument_exact, ih, ArgumentsRel]

end Yulang.CommonRecursiveNominalIntervals
