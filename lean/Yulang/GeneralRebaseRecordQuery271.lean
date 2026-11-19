import Yulang.GeneralRebaseRecordQueryShape271
import Yulang.GeneralRebaseOriginNegativeTags270

namespace Yulang.GeneralRebaseRecordQuery271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Cyclic)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots shape)
open GeneralRebaseOriginNegativeTags270 (sourceSlot sourceSlot_sound)
open GeneralRebaseRecordAlignment271 (visibleSet)
open GeneralRebaseRecordQueryShape271 (Dead query_over out_of_range hidden different_set)
open GeneralRebasePartialBool268 (Answer Reflect)

inductive Result (α : Type) where
 | unknown
 | dead
 | child (slot : α)
 deriving DecidableEq

def raw (state : State roles) (slot : Slots state) (read : List Nat) (j : Nat) : Result (Slots state) :=
 match read[j]? with
 | none => .dead
 | some key =>
   if key ∈ read.take j then .dead
   else
     match (Raw state).view.heads slot with
     | .structural kind children =>
       match shape state kind with
       | .record keys =>
         if visibleSet keys read then
           match (List.finRange (shape state kind).arity).find? (fun i => keys[i.val]? == some key) with
           | some found => .child (children found)
           | none => .unknown
         else .dead
       | _ => .unknown
     | _ => .unknown

def Valid (state : State roles) (o : Origin) : Result (Slots state) → Prop
 | .unknown => True
 | .dead => Dead state o
 | .child s => Equal state o (origin state s)

theorem raw_sound (state : State roles) (full : ∃ m, Models state m) (slot : Slots state) (read : List Nat) (j : Nat) :
 Valid state (.structural (origin state slot) (.record read) j) (raw state slot read j) := by
 unfold raw
 split
 · rename_i q
   exact out_of_range state _ read j q full
 · rename_i key q
   split
   · exact hidden state _ read j key q (by assumption) full
   · rename_i visible
     split
     · rename_i kind children shapeInfo
       split
       · rename_i keys record
         split
         · rename_i check
           split
           · rename_i hit found
             have query : keys[hit.val]? = some key :=
               beq_iff_eq.mp (List.find?_some (p := fun i : Fin (shape state kind).arity => keys[i.val]? == some key) found)
             exact query_over state slot kind keys read children record shapeInfo hit j key query q check visible
           · trivial
         · rename_i off
           exact different_set state slot kind keys read children record shapeInfo j (Bool.eq_false_iff.mpr off) full
       · trivial
     · trivial

def locate (state : State roles) : Origin → Result (Slots state)
 | .structural (.source identity) (.record read) j =>
   match sourceSlot state identity with
   | some s => raw state s read j
   | none => .unknown
 | _ => .unknown

theorem locate_sound (state : State roles) (full : ∃ m, Models state m) (o : Origin) :
 Valid state o (locate state o) := by
 unfold locate
 split
 · rename_i identity read j
   split
   · rename_i s found
     have e := raw_sound state full s read j
     rw [sourceSlot_sound state identity s found] at e
     exact e
   · trivial
 · trivial

theorem dead_no_cycle (state : State roles) (o : Origin) (dead : Dead state o) :
 ¬ Cyclic state o := by
 rintro ⟨⟨target,⟨parent,test,index,head,pre,post⟩,path⟩,m,ok⟩
 exact dead parent pre

end Yulang.GeneralRebaseRecordQuery271
