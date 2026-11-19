import Yulang.GeneralRebaseLocalOriginPocket271

namespace Yulang.GeneralRebaseScalarAtoms271
open GeneralSourceState (State)
open PresenceNormalForm (Atom)
open GeneralNormalizedObservation (Rewrites)
open Core.PresenceGeneration (TyTerm)

def left (slot : Fin n) : Atom (Fin n) → Option Inference.Base
 | .tyLe (.var i) (.base b) => if i = slot then some b else none
 | _ => none

def right (slot : Fin n) : Atom (Fin n) → Option Inference.Base
 | .tyLe (.base b) (.var i) => if i = slot then some b else none
 | _ => none

theorem one (slot : Fin n) (atom : Atom (Fin n)) (b : Inference.Base) (found : left slot atom = some b) :
 atom = .tyLe (.var slot) (.base b) := by
 unfold left at found
 split at found
 · split at found
   · rename_i k v eq h
     cases h
     cases Option.some.inj found
     rfl
   · contradiction
 · contradiction

theorem other (slot : Fin n) (atom : Atom (Fin n)) (b : Inference.Base) (found : right slot atom = some b) :
 atom = .tyLe (.base b) (.var slot) := by
 unfold right at found
 split at found
 · split at found
   · rename_i v k eq h
     cases h
     cases Option.some.inj found
     rfl
   · contradiction
 · contradiction

def candidate (base : State) (slot : Fin base.slots) : Option Inference.Base :=
 let forwards := base.ordinary.filterMap (left slot)
 let backwards := base.ordinary.filterMap (right slot)
 forwards.find? (fun b => decide (b ∈ backwards))

theorem checks (base : State) (slot : Fin base.slots) (b : Inference.Base)
 (found : candidate base slot = some b) :
 Rewrites base (.var slot) (.base b) := by
 have onLeft : b ∈ base.ordinary.filterMap (left slot) := List.mem_of_find?_eq_some found
 have onRight : b ∈ base.ordinary.filterMap (right slot) := of_decide_eq_true
   (List.find?_some (p:=fun x => decide (x ∈ base.ordinary.filterMap (right slot))) found)
 obtain ⟨a,member,detected⟩ := List.mem_filterMap.mp onLeft
 obtain ⟨z,also,reverse⟩ := List.mem_filterMap.mp onRight
 exact .ordinary ((one slot a b detected) ▸ member) ((other slot z b reverse) ▸ also)

end Yulang.GeneralRebaseScalarAtoms271
