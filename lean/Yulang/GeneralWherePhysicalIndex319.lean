import Yulang.GeneralWhereOriginHeadAgree318
import Yulang.GeneralWhereOriginLayoutContract318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 5000000
namespace Yulang.GeneralWherePhysicalIndex319
open GeneralSourceState (State)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (RowTerm TyTerm)

abbrev old (n : Nat) (i : Fin m) : Fin (m+n) := i.castAdd n
abbrev new (m : Nat) (i : Fin n) : Fin (m+n) := i.natAdd m

theorem old_injective (n : Nat) : Function.Injective (old (m := m) n) :=
  fun _ _ eq => Fin.ext (congrArg (fun i : Fin (m+n) => i.val) eq)

theorem new_injective (m : Nat) : Function.Injective (new (n := n) m) :=
  fun _ _ eq => Fin.ext (Nat.add_left_cancel (congrArg (fun i : Fin (m+n) => i.val) eq))

theorem join_injective {oldId : Fin m → Nat} {newId : Fin n → Nat}
    (left : Function.Injective oldId) (right : Function.Injective newId)
    (apart : ∀ i j, oldId i ≠ newId j) :
    Function.Injective (Fin.addCases oldId newId : Fin (m+n) → Nat) := by
  intro a b
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) b
  · simp only [Fin.addCases_left]
    exact fun eq => congrArg (old n) (left eq)
  · simp only [Fin.addCases_left,Fin.addCases_right]
    exact fun eq => False.elim (apart i j eq)
  · simp only [Fin.addCases_left,Fin.addCases_right]
    exact fun eq => False.elim (apart j i eq.symm)
  · simp only [Fin.addCases_right]
    exact fun eq => congrArg (new m) (right eq)

def shape (f : Fin m → Fin n) : GeneralSourceState.Shape m → GeneralSourceState.Shape n
  | .pair => .pair
  | .required label => .required label
  | .record label => .record label
  | .variant tag => .variant tag
  | .arrow a b => .arrow (a.rename f) (b.rename f)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty

theorem shape_arity (f : Fin m → Fin n) (s : GeneralSourceState.Shape m) :
    (shape f s).arity = s.arity := by cases s <;> rfl

def head (f : Fin m → Fin n) {shapes : Fin k → GeneralSourceState.Shape m}
    (h : GeneralSourceState.Head shapes) : GeneralSourceState.Head (shape f ∘ shapes) :=
  match h with
  | .unresolved => .unresolved
  | .scalar b => .scalar b
  | .structural tag children => .structural tag
      (fun i => f (children (Fin.cast (shape_arity f (shapes tag)) i)))

theorem shape_rename_term (f : Fin m → Fin n) (s : GeneralSourceState.Shape m)
    (c : Fin s.arity → Fin m) :
    (shape f s).term (fun i => f (c (Fin.cast (shape_arity f s) i))) = (s.term c).rename f := by
  cases s <;> rfl

theorem head_rename_term (f : Fin m → Fin n) {shapes : Fin k → GeneralSourceState.Shape m}
    (h : GeneralSourceState.Head shapes) :
    (head f h).equation = h.equation.map (fun term => term.rename f) := by
  cases h with
  | unresolved => rfl
  | scalar _ => rfl
  | structural i c =>
    change some ((shape f (shapes i)).term _) = _
    exact congrArg some (shape_rename_term f (shapes i) c)

theorem old_locate {before after : State} (embed : Fin before.slots → Fin after.slots)
    (preserved : ∀ i, after.source (embed i) = before.source i)
    {id} {i : Fin before.slots} (was : sourceSlot before id = some i) :
    sourceSlot after id = some (embed i) :=
  (sourceSlot_exact ..).mpr ((preserved i).trans ((sourceSlot_exact ..).mp was))

end Yulang.GeneralWherePhysicalIndex319
