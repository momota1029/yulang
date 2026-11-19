import Yulang.GeneralRebaseNestedQueryCongruence271
import Yulang.GeneralRebaseStructuralRepresentative271

namespace Yulang.GeneralRebaseNestedRecordQuery271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseNominalOrigin269 (origin)
open GeneralRebaseStructuralOrigin270 (Slots)
open GeneralRebaseOriginNegativeTags270 (sourceSlot sourceSlot_sound)
open GeneralRebaseNestedQueryCongruence271 (Operation applyOp transport_equal transport_dead)
open GeneralRebaseRecordQuery271 (Result Valid locate locate_sound dead_no_cycle)
open GeneralRebasePartialBool268 (Answer Reflect)

def fromOption : Option α → Result α
 | some value => .child value
 | none => .unknown

def next (state : State roles) (slot : Slots state) (op : Operation) : Result (Slots state) :=
 let o := applyOp op (origin state slot)
 match op with
 | .structural (.record _) _ => locate state o
 | .structural _ _ => fromOption (GeneralRebaseStructuralRepresentative271.structural state o)
 | .nominal _ _ => fromOption (GeneralRebaseOriginRepresentative270.representative state o)

theorem next_sound (state : State roles) (full : ∃ m, Models state m)
 (slot : Slots state) (op : Operation) : Valid state (applyOp op (origin state slot)) (next state slot op) := by
 have option_sound (o : Origin) (a : Option (Slots state))
   (yes : ∀ t, a = some t → GeneralNominalVersionedCycles232.Equal state o (origin state t)) :
   Valid state o (fromOption a) := by
   cases a with
   | none => trivial
   | some val => exact yes val rfl
 cases op with
 | nominal n i =>
   apply option_sound
   exact fun t h => GeneralRebaseOriginRepresentative270.representative_sound state _ t h
 | structural s i =>
   cases s with
   | record labels => exact locate_sound state full _
   | pair | variant _ | exactEmpty =>
     all_goals
       apply option_sound
       exact fun t h => GeneralRebaseStructuralRepresentative271.structural_sound state _ t h

def follow (state : State roles) (op : Operation) : Result (Slots state) → Result (Slots state)
 | .child slot => next state slot op
 | _ => .unknown

def resolve (state : State roles) : Origin → Result (Slots state)
 | .source id => fromOption (sourceSlot state id)
 | .structural parent shape i => follow state (.structural shape i) (resolve state parent)
 | .nominal parent name i => follow state (.nominal name i) (resolve state parent)

theorem follow_sound (state : State roles) (full : ∃ m, Models state m) (op : Operation)
 (parent : Origin) (p : Result (Slots state)) (valid : Valid state parent p) :
 Valid state (applyOp op parent) (follow state op p) := by
 cases p with
 | unknown | dead => trivial
 | child s =>
   have checked := next_sound state full s op
   change Valid state (applyOp op parent) (next state s op)
   cases q : next state s op with
   | unknown => trivial
   | dead =>
     rw [q] at checked
     exact transport_dead state op valid checked
   | child child =>
     rw [q] at checked
     exact transport_equal state op (GeneralRebaseOriginCongruence269.equal_symm valid) checked

theorem resolve_sound (state : State roles) (full : ∃ m, Models state m) (o : Origin) :
 Valid state o (resolve state o) := by
 induction o with
 | source id =>
   unfold resolve
   cases h : sourceSlot state id with
   | none => trivial
   | some s =>
     change GeneralNominalVersionedCycles232.Equal state (.source id) (origin state s)
     rw [sourceSlot_sound state id s h]
     exact fun m ok => GeneralNominalOriginTerms.source_self m id
 | structural parent shape i ih =>
   exact follow_sound state full (.structural shape i) parent _ ih
 | nominal parent name i ih =>
   exact follow_sound state full (.nominal name i) parent _ ih

def inspect (state : State roles) (o : Origin) : Answer :=
 match resolve state o with
 | .dead => some false
 | .child s => GeneralRebaseRecordRouting271.inspect state (origin state s)
 | .unknown => GeneralRebaseRecordRouting271.inspect state o

theorem inspect_sound (state : State roles) (full : ∃ m, Models state m) (o : Origin) :
 Reflect (Cyclic state o) (inspect state o) := by
 have r := resolve_sound state full o
 unfold inspect
 split
 · rename_i checked
   rw [checked] at r
   exact dead_no_cycle state o r
 · rename_i s checked
   rw [checked] at r
   exact GeneralRebasePartialFinite268.transfer (GeneralRebaseRecordRouting271.cyclic_congr state r).symm
      (GeneralRebaseRecordRouting271.inspect_sound state full (origin state s))
 · exact GeneralRebaseRecordRouting271.inspect_sound state full o

end Yulang.GeneralRebaseNestedRecordQuery271
