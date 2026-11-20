import Yulang.GeneralRebaseFiniteRowReads285

namespace Yulang.GeneralRebaseRowBasis298
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceSubstitutionSupport244 (rowSources)
open GeneralPresenceUsedSupport245 (rowReads)
open GeneralRebaseFiniteRowReads285 (local_row_eval local_type_eval equationRows)
open GeneralNominalCommonBridge (Assignment)

theorem type_eval_equal (m : Model) (a b : Name → Comp m)
    (types : ∀ n, (a n).1 = (b n).1) (term : TyTerm Name)
    (rows : ∀ n ∈ rowReads term, (a n).2 = (b n).2) :
    term.eval m a = term.eval m b :=
  local_type_eval m a b term (fun n _ => types n) rows

def atomRowReads : Atom Name → List Name
 | .tyLe a b => rowReads a ++ rowReads b
 | .rowLe a b => rowSources a ++ rowSources b

def listRowReads (atoms : List (Atom Name)) := atoms.flatMap atomRowReads

theorem atom_iff (m : Model) (a b : Name → Comp m)
    (types : ∀ n, (a n).1 = (b n).1) (q : Atom Name)
    (rows : ∀ n ∈ atomRowReads q, (a n).2 = (b n).2) :
    q.Holds m a ↔ q.Holds m b := by
  cases q with
  | tyLe lo hi =>
    simp only [Atom.Holds,
      type_eval_equal m a b types lo (fun n h => rows n (List.mem_append_left _ h)),
      type_eval_equal m a b types hi (fun n h => rows n (List.mem_append_right _ h))]
  | rowLe lo hi =>
    simp only [Atom.Holds,
      local_row_eval m a b lo (fun n h => rows n (List.mem_append_left _ h)),
      local_row_eval m a b hi (fun n h => rows n (List.mem_append_right _ h))]

theorem all_iff (m : Model) (a b : Name → Comp m)
    (types : ∀ n, (a n).1 = (b n).1) (atoms : List (Atom Name))
    (rows : ∀ n ∈ listRowReads atoms, (a n).2 = (b n).2) :
    All m a atoms ↔ All m b atoms := by
  unfold All
  apply forall_congr'; intro atom
  apply forall_congr'; intro member
  exact atom_iff m a b types atom (fun n h => rows n (List.mem_flatMap.mpr ⟨atom,member,h⟩))

theorem equation_iff (q : GeneralNominalRebaseEffectView243.Equation) (a b : Assignment)
    (types : ∀ n, (a n).1 = (b n).1)
    (rows : ∀ n ∈ equationRows q, (a n).2 = (b n).2) :
    q.Holds a ↔ q.Holds b :=
  GeneralRebaseFiniteRowReads285.equation_iff q a b (fun n _ => types n) rows

end Yulang.GeneralRebaseRowBasis298
