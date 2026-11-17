import Yulang.GeneralPresenceUsedSupport245
import Yulang.GeneralPresenceModelCongruence245

/-! Literal consumer preservation tracks typed reads separately from rows.
Private type names may still occur in row expressions when all rows are kept.
These syntax-level support laws do not enumerate actual solver metadata. -/
namespace Yulang.GeneralPresenceConsumerSupport246
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceUsedSupport245 (typedReads)
variable {Name : Type}

theorem type_eval_equal (model : Model) (first last : Name → Comp model)
    (rows : ∀ name, (first name).2 = (last name).2) (term : TyTerm Name)
    (types : ∀ name ∈ typedReads term, (first name).1 = (last name).1) :
    term.eval model first = term.eval model last := by
  induction term with
  | var name => exact types name (by simp [typedReads])
  | base | bottom | top | emptyRecord | exactEmpty => rfl
  | union a b one two =>
    simp only [TyTerm.eval,one (fun n h => types n (List.mem_append_left _ h)),
      two (fun n h => types n (List.mem_append_right _ h))]
  | inter a b one two =>
    simp only [TyTerm.eval,one (fun n h => types n (List.mem_append_left _ h)),
      two (fun n h => types n (List.mem_append_right _ h))]
  | pair a b one two =>
    simp only [TyTerm.eval,one (fun n h => types n (List.mem_append_left _ h)),
      two (fun n h => types n (List.mem_append_right _ h))]
  | record label a b one two =>
    simp only [TyTerm.eval,one (fun n h => types n (List.mem_append_left _ h)),
      two (fun n h => types n (List.mem_append_right _ h))]
  | recordDefault label a b one two =>
    simp only [TyTerm.eval,one (fun n h => types n (List.mem_append_left _ h)),
      two (fun n h => types n (List.mem_append_right _ h))]
  | required label a ih => simp only [TyTerm.eval,ih types]
  | variant label a ih => simp only [TyTerm.eval,ih types]
  | arrow a incoming b outgoing one two =>
    simp only [TyTerm.eval,one (fun n h => types n (List.mem_append_left _ h)),
      two (fun n h => types n (List.mem_append_right _ h)),
      GeneralPresenceModelCongruence245.row_eval_equal model first last rows]

def atomTypedReads : Atom Name → List Name
  | .tyLe a b => typedReads a ++ typedReads b
  | .rowLe _ _ => []

def listTypedReads (atoms : List (Atom Name)) : List Name := atoms.flatMap atomTypedReads

theorem atom_holds_iff (model : Model) (first last : Name → Comp model)
    (rows : ∀ name, (first name).2 = (last name).2) (atom : Atom Name)
    (types : ∀ name ∈ atomTypedReads atom, (first name).1 = (last name).1) :
    atom.Holds model first ↔ atom.Holds model last := by
  cases atom with
  | tyLe a b =>
    simp only [Atom.Holds,
      type_eval_equal model first last rows a (fun n h => types n (List.mem_append_left _ h)),
      type_eval_equal model first last rows b (fun n h => types n (List.mem_append_right _ h))]
  | rowLe a b =>
    simp only [Atom.Holds,GeneralPresenceModelCongruence245.row_eval_equal model first last rows]

theorem all_iff (model : Model) (first last : Name → Comp model)
    (rows : ∀ name, (first name).2 = (last name).2) (atoms : List (Atom Name))
    (types : ∀ name ∈ listTypedReads atoms, (first name).1 = (last name).1) :
    All model first atoms ↔ All model last atoms := by
  have perAtom (atom : Atom Name) (member : atom ∈ atoms) :
      atom.Holds model first ↔ atom.Holds model last :=
    atom_holds_iff model first last rows atom
      (fun name present => types name (List.mem_flatMap.mpr ⟨atom,member,present⟩))
  constructor
  · intro valid atom member
    exact (perAtom atom member).mp (valid atom member)
  · intro valid atom member
    exact (perAtom atom member).mpr (valid atom member)

theorem all_outside_iff (model : Model) (first last : Name → Comp model)
    (privateNames : Name → Prop)
    (rows : ∀ name, (first name).2 = (last name).2)
    (outsideValues : ∀ name, ¬ privateNames name → (first name).1 = (last name).1)
    (atoms : List (Atom Name))
    (outsideReads : ∀ name ∈ listTypedReads atoms, ¬ privateNames name) :
    All model first atoms ↔ All model last atoms :=
  all_iff model first last rows atoms (fun name present => outsideValues name (outsideReads name present))

end Yulang.GeneralPresenceConsumerSupport246
