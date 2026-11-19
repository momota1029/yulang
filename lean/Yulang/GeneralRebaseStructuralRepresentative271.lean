import Yulang.GeneralRebaseStructuralCompare271

namespace Yulang.GeneralRebaseStructuralRepresentative271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (project)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots shape projected_equals)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseOriginNegativeTags270 (sourceSlot sourceSlot_sound onSlots onSlots_sound)
open GeneralRebaseOriginCongruence269 (equal_symm equal_trans)

def structural (state : State roles) : Origin → Option (Slots state)
 | .structural (.source id) lit idx => do
   let s ← sourceSlot state id
   match (Raw state).view.heads s with
   | .structural kind kids =>
     if shape state kind = lit then
       if valid : idx < (shape state kind).arity then some (kids ⟨idx, valid⟩) else none
     else none
   | _ => none
 | _ => none

theorem structural_sound (state : State roles) (o : Origin) (r : Slots state)
 (known : structural state o = some r) : Equal state o (origin state r) := by
 unfold structural at known
 split at known
 · rename_i id lit idx
   cases source : sourceSlot state id with
   | none => simp [source] at known
   | some s =>
     simp only [source] at known
     change (match (Raw state).view.heads s with
       | .structural kind kids =>
         if shape state kind = lit then
         if valid : idx < (shape state kind).arity then some (kids ⟨idx,valid⟩) else none
         else none
       | _ => none) = some r at known
     split at known
     · rename_i k children recorded
       split at known
       · rename_i same
         split at known
         · rename_i valid
           cases Option.some.inj known
           have eq := projected_equals state s k children recorded ⟨idx,valid⟩
           rw [sourceSlot_sound state id s source] at eq
           change Equal state (.structural (.source id) (shape state k) idx) _ at eq
           subst lit
           exact eq
         · contradiction
       · contradiction
     · contradiction
 · contradiction

def representative (state : State roles) (o : Origin) : Option (Slots state) :=
 (GeneralRebaseOriginRepresentative270.representative state o).or (structural state o)

theorem representative_sound (state : State roles) (o : Origin) (s : Slots state)
 (found : representative state o = some s) : Equal state o (origin state s) := by
 unfold representative at found
 cases prev : GeneralRebaseOriginRepresentative270.representative state o with
 | none =>
   exact structural_sound state o s (by simpa [prev,Option.or] using found)
 | some old =>
   have same : old = s := Option.some.inj (by simpa [prev,Option.or] using found)
   exact same ▸ GeneralRebaseOriginRepresentative270.representative_sound state o old prev

def compareSlots (state : State roles) (a b : Slots state) : Answer :=
 (onSlots state a b).or (GeneralRebaseStructuralCompare271.distinguish state a b)

theorem compareSlots_sound (state : State roles) (m : ∃ assign, Models state assign) (a b : Slots state) :
 Reflect (Equal state (origin state a) (origin state b)) (compareSlots state a b) := by
 unfold compareSlots
 cases old : onSlots state a b with
 | none => exact GeneralRebaseStructuralCompare271.distinguish_sound state m a b
 | some value => simpa [old,Option.or] using onSlots_sound state a b m

def compare (state : State roles) (a b : Origin) : Answer :=
 (GeneralRebaseOriginRepresentative270.compare state a b).or
 (match representative state a, representative state b with
  | some x,some y => compareSlots state x y
  | _,_ => none)

theorem compare_sound (state : State roles) (inhabited : ∃ m, Models state m) (a b : Origin) :
 Reflect (Equal state a b) (compare state a b) := by
 unfold compare
 cases previous : GeneralRebaseOriginRepresentative270.compare state a b with
 | some answer =>
   simpa [previous,Option.or] using GeneralRebaseOriginRepresentative270.compare_sound state inhabited a b
 | none =>
   simp only [Option.or]
   split
   · rename_i x y left right
     have xEq := representative_sound state a x left
     have yEq := representative_sound state b y right
     exact GeneralRebasePartialFinite268.transfer (show Equal state a b ↔ Equal state (origin state x) (origin state y) from
       ⟨fun e => equal_trans (equal_symm xEq) (equal_trans e yEq),
         fun e => equal_trans xEq (equal_trans e (equal_symm yEq))⟩).symm
       (compareSlots_sound state inhabited x y)
   · trivial

end Yulang.GeneralRebaseStructuralRepresentative271
