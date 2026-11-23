import Yulang.GeneralDeclarativeWitnessFullIntervals357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessSparseIntervals357 (Legal visited)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives ContextDerivesArguments ContextDerivesArgument)
open GeneralNominalCommonBridge (Assignment)
open CommonRecursiveNominalIntervals (Endpoint Bounds Argument ContextWellFormed childContext effectiveParameter)
open CommonDeclaredNominalInspection (Parameter Registry)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom)

/- An independent, model-free derivation of the declared-mode
obligations. Leaves cite actual ordinary atoms; the rules do not invoke
the executable comparison, a selected implementation, or a model. -/
mutual
inductive Compare (s : GeneralDeclarativeHead320.State) (table : Registry) :
    Bool → Endpoint Nat → Endpoint Nat → Type where
  | ordinary {a b : TyTerm Nat} : Atom.tyLe a b ∈ s.normal.ordinary →
      Compare s table context (.ordinary a) (.ordinary b)
  | nominal {first last row} :
      table[name]? = some row → CompareArguments s table context row first last →
      Compare s table context (.nominal name first) (.nominal name last)

inductive CompareArguments (s : GeneralDeclarativeHead320.State) (table : Registry) :
    Bool → List Parameter → List (Argument Nat) → List (Argument Nat) → Type where
  | nil : CompareArguments s table context [] [] []
  | cons :
      CompareArgument s table (childContext context p) (effectiveParameter context p) a b →
      CompareArguments s table context ps as bs →
      CompareArguments s table context (p::ps) (a::as) (b::bs)

inductive CompareArgument (s : GeneralDeclarativeHead320.State) (table : Registry) :
    Bool → Parameter → Argument Nat → Argument Nat → Type where
  | covariantValue : Compare s table context a b →
      CompareArgument s table context ⟨.value,.covariant⟩ (.inl (.point a)) (.inl (.point b))
  | contravariantValue : Compare s table context b a →
      CompareArgument s table context ⟨.value,.contravariant⟩ (.inl (.point a)) (.inl (.point b))
  | invariantValue {a b : Bounds (Endpoint Nat)} :
      Compare s table context a.lower a.upper → Compare s table context b.lower b.upper →
      Compare s table context a.lower b.upper → Compare s table context b.lower a.upper →
      CompareArgument s table context ⟨.value,.invariant⟩ (.inl a) (.inl b)
  | unusedValue (a b : Bounds (Endpoint Nat)) :
      CompareArgument s table context ⟨.value,.unused⟩ (.inl a) (.inl b)
  | covariantRow {a b : RowTerm Nat} : Atom.rowLe a b ∈ s.normal.ordinary →
      CompareArgument s table context ⟨.row,.covariant⟩ (.inr (.point a)) (.inr (.point b))
  | contravariantRow {a b : RowTerm Nat} : Atom.rowLe b a ∈ s.normal.ordinary →
      CompareArgument s table context ⟨.row,.contravariant⟩ (.inr (.point a)) (.inr (.point b))
  | invariantRow {a b : Bounds (RowTerm Nat)} :
      Atom.rowLe a.lower a.upper ∈ s.normal.ordinary → Atom.rowLe b.lower b.upper ∈ s.normal.ordinary →
      Atom.rowLe a.lower b.upper ∈ s.normal.ordinary → Atom.rowLe b.lower a.upper ∈ s.normal.ordinary →
      CompareArgument s table context ⟨.row,.invariant⟩ (.inr a) (.inr b)
  | unusedRow (a b : Bounds (RowTerm Nat)) :
      CompareArgument s table context ⟨.row,.unused⟩ (.inr a) (.inr b)
end

theorem compare_sound {s table context lo hi} (read : Compare s table context lo hi)
    (m : Assignment) (fit : Models s m) : ContextDerives table m context lo hi := by
  exact Compare.rec
    (motive_1 := fun c a b _ => ContextDerives table m c a b)
    (motive_2 := fun c ps xs ys _ => ContextDerivesArguments table m c ps xs ys)
    (motive_3 := fun c p a b _ => ContextDerivesArgument table m c p a b)
    (fun found => .ordinary (fit.1.1 _ found))
    (fun row _ ih => .nominal row ih)
    (fun {c} => .nil c)
    (fun _ _ h t => .cons h t)
    (fun _ h => .covariantValue h)
    (fun _ h => .contravariantValue h)
    (fun _ _ _ _ a b c d => .invariantValue a b c d)
    (fun {c} a b => .unusedValue c a b)
    (fun p => .covariantRow (fit.1.1 _ p))
    (fun p => .contravariantRow (fit.1.1 _ p))
    (fun a b c d => .invariantRow (fit.1.1 _ a) (fit.1.1 _ b) (fit.1.1 _ c) (fit.1.1 _ d))
    (fun {c} a b => .unusedRow c a b)
    read

/-- The sparse source, endpoint wellformedness and ordinary entailment
are independent obligations, including syntax at unused positions. A
dense default slot is not authority for a name. -/
structure DeclaredComparison (e : Environment) (s : GeneralDeclarativeHead320.State)
    (table : Registry) (context : Bool) (lo hi : Endpoint Nat) where
  actualSource : ∀ site ∈ visited lo ++ visited hi, Legal e table site
  left : ContextWellFormed table context lo
  right : ContextWellFormed table context hi
  compared : Compare s table context lo hi

theorem in_same_model {e s table context lo hi} (h : DeclaredComparison e s table context lo hi)
    (m : Assignment) (fit : Models s m) :
    ContextWellFormed table context lo ∧ ContextWellFormed table context hi ∧ ContextDerives table m context lo hi :=
  ⟨h.left,h.right,compare_sound h.compared m fit⟩

end Yulang.GeneralDeclarativeI65
