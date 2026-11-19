import Yulang.GeneralRebaseRecordRouting271

namespace Yulang.GeneralRebaseNestedQueryCongruence271
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralNominalOriginTerms (Same same_symm)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralRebaseRecordQueryShape271 (Dead)

inductive Operation where
 | structural (shape : GeneralNormalizedObservation.Shape) (index : Nat)
 | nominal (name index : Nat)

def applyOp (op : Operation) (focus : Origin) : Origin :=
 match op with
 | .structural s i => .structural focus s i
 | .nominal n i => .nominal focus n i

theorem transport_observation (m : Assignment) (op : Operation) (same : Same m first last)
 (known : Observes m (applyOp op first) value) : Observes m (applyOp op last) value := by
 obtain ⟨v,read⟩ := same.2.1
 cases op with
 | structural shape j =>
   cases known with
   | structural parent len eq atVal =>
     have matchParent := same.2.2 _ v parent read
     exact .structural read len ⟨subtype_trans matchParent.2 eq.1,subtype_trans eq.2 matchParent.1⟩ atVal
 | nominal name j =>
   cases known with
   | nominal parent eq atVal =>
     have matchParent := same.2.2 _ v parent read
     exact .nominal read ⟨subtype_trans matchParent.2 eq.1,subtype_trans eq.2 matchParent.1⟩ atVal

theorem transport_equal (state : State roles) (op : Operation) (same : Equal state first last)
 (result : Equal state (applyOp op first) target) : Equal state (applyOp op last) target := by
 intro m valid
 have parent := same m valid
 have child := result m valid
 obtain ⟨v,atOld⟩ := child.1
 refine ⟨⟨v,transport_observation m op parent atOld⟩,child.2.1,?_⟩
 intro x y newSeen targetSeen
 exact child.2.2 x y (transport_observation m op (same_symm parent) newSeen) targetSeen

theorem transport_dead (state : State roles) (op : Operation) (same : Equal state first last)
 (dead : Dead state (applyOp op last)) : Dead state (applyOp op first) :=
 fun target result => dead target (transport_equal state op same result)

end Yulang.GeneralRebaseNestedQueryCongruence271
