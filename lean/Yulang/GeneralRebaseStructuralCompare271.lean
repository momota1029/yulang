import Yulang.GeneralRebaseRecordEdge271
import Yulang.GeneralRebaseOriginRepresentative270

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseStructuralCompare271
open CommonNominalFullCarrier
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Head)
open GeneralNominalRecursiveInspection (Origin Test shapeValue)
open GeneralNominalCommonBridge (Assignment)
open GeneralNormalizedObservation (Shape)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots shape)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseOriginNegativeTags270 (test test_sound sourceSlot sourceSlot_sound)
open GeneralRebaseOriginCongruence269 (equal_symm equal_trans)

def contradicts : Test → Test → Bool
 | .structural (.record xs), .structural (.record ys) => xs != ys
 | .structural .exactEmpty, .structural (.record _) => true
 | .structural (.record _), .structural .exactEmpty => true
 | _, _ => false

def canonical : Test → Prop
 | .structural s => s.Canonical
 | _ => True

theorem test_canonical (state : State roles) (slot : Slots state) (lit : Test)
 (known : test state slot = some lit) : canonical lit := by
 unfold test at known
 split at known
 · rename_i d recorded
   have e := Option.some.inj known
   rw [← e]
   trivial
 · split at known
   · rename_i k args recorded
     have e := Option.some.inj known
     rw [← e]
     exact (Raw state).view.canonical k
   · rename_i scalar recorded
     have e := Option.some.inj known
     rw [← e]
     trivial
   · contradiction

theorem shape_contradiction (a b : Shape) (xs ys : List Ty) (xLen : xs.length = a.arity) (yLen : ys.length = b.arity)
 (xCanonical : a.Canonical) (yCanonical : b.Canonical)
 (yes : contradicts (.structural a) (.structural b) = true) :
 ¬ Equivalent (shapeValue a xs) (shapeValue b ys) := by
 cases a <;> cases b <;> try cases yes
 case record.record left right =>
   intro rel
   have equal := GeneralNominalRecordInversion.record_signatures left right xs ys xCanonical yCanonical xLen yLen rel
   subst right
   simp [contradicts] at yes
 case record.exactEmpty labels =>
   rw [GeneralNominalRecordInversion.record_shape labels xs xLen]
   exact GeneralNominalFiniteHeadInversion.record_not_exactEmpty _
 case exactEmpty.record labels =>
   rw [GeneralNominalRecordInversion.record_shape labels ys yLen]
   exact fun equivalent => GeneralNominalFiniteHeadInversion.record_not_exactEmpty _ ⟨equivalent.2,equivalent.1⟩

theorem contradicts_sound (state : State roles) (a b : Slots state)
 (t u : Test) (xKnown : test state a = some t) (yKnown : test state b = some u)
 (yes : contradicts t u = true) (witness : ∃ m, Models state m) :
 ¬ Equal state (origin state a) (origin state b) := by
 obtain ⟨m,valid⟩ := witness
 intro equal
 have l := (test_sound state a t xKnown m valid).2 _ (.source _)
 have r := (test_sound state b u yKnown m valid).2 _ (.source _)
 have equality := (equal m valid).2.2 _ _ (.source _) (.source _)
 cases t <;> cases u <;> try cases yes
 case structural.scalar x y => cases x <;> cases yes
 case structural.nominal x _ _ => cases x <;> cases yes
 case structural.structural x y =>
   obtain ⟨xs,szX,certificateX⟩ := l
   obtain ⟨ys,szY,certificateY⟩ := r
   exact shape_contradiction x y xs ys szX szY (test_canonical state a _ xKnown) (test_canonical state b _ yKnown) yes
     ⟨subtype_trans certificateX.2 (subtype_trans equality.1 certificateY.1),
      subtype_trans certificateY.2 (subtype_trans equality.2 certificateX.1)⟩

def distinguish (state : State roles) (x y : Slots state) : Answer :=
 match test state x, test state y with
 | some a,some b => if contradicts a b then some false else none
 | _,_ => none

theorem distinguish_sound (state : State roles) (full : ∃ m, Models state m) (x y : Slots state) :
 Reflect (Equal state (origin state x) (origin state y)) (distinguish state x y) := by
 unfold distinguish
 split
 · rename_i a b first last
   split
   · exact contradicts_sound state x y a b first last (by assumption) full
   · trivial
 · trivial

end Yulang.GeneralRebaseStructuralCompare271
