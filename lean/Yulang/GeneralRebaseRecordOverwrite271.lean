import Yulang.GeneralRebaseRecordLookup271

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordOverwrite271
open CommonNominalFullCarrier
open GeneralNominalStructuralReadback (recordValues)
open GeneralRebaseRecordLookup271 (first)
open CommonNominalFullDemand (MaskedProbeStep ProbeAt Environment Observation)

def finite (depth : Nat) (xs : List (Nat × Ty)) : CommonNominalFullDemand.Ty Row :=
 xs.foldr (fun entry rest => .record entry.1
   (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node entry.2)) rest) .emptyRecord

theorem observed (depth : Nat) (xs : List (Nat × Ty)) :
 observeTy depth (recordValues xs) = finite depth xs := by
 induction xs with
 | nil => rfl
 | cons item rest ih =>
   change CommonNominalFinite.Ty.record item.1 _ (observeTy depth (recordValues rest)) = _
   rw [ih]
   rfl

theorem fieldStep (depth : Nat) (xs : List (Nat × Ty)) (env : Environment Row)
 (order : CommonNominalFullDemand.Ty Row → CommonNominalFullDemand.Ty Row → Prop)
 (label : Nat) (obs : Observation Row) :
 MaskedProbeStep Common.rowLe env order [] (finite depth xs) (.field label obs) ↔
 match first label xs with
 | none => False
 | some value => MaskedProbeStep Common.rowLe env order []
     (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node value)) obs := by
 induction xs with
 | nil => rfl
 | cons head rest ih =>
   obtain ⟨k,v⟩ := head
   change MaskedProbeStep Common.rowLe env order [] (.record k _ (finite depth rest)) (.field label obs) ↔ _
   by_cases eq : label = k <;> simp only [first,CommonNominalFullDemand.MaskedProbeStep,eq,List.not_mem_nil,not_false_eq_true,and_true,ite_true,ite_false,ih]

theorem optStep (depth : Nat) (xs : List (Nat × Ty)) (env : Environment Row)
 (order : CommonNominalFullDemand.Ty Row → CommonNominalFullDemand.Ty Row → Prop)
 (label : Nat) (obs : Observation Row) :
 MaskedProbeStep Common.rowLe env order [] (finite depth xs) (.optional label obs) ↔
 (match first label xs with
 | none => False
 | some value => MaskedProbeStep Common.rowLe env order []
     (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node value)) obs) ∨
  obs = .trivial := by
 induction xs with
 | nil => simp [finite,first,CommonNominalFullDemand.MaskedProbeStep]
 | cons head rest ih =>
   obtain ⟨k,v⟩ := head
   change MaskedProbeStep Common.rowLe env order [] (.record k _ (finite depth rest)) (.optional label obs) ↔ _
   by_cases eq : label = k
   · subst k
     simp only [CommonNominalFullDemand.MaskedProbeStep,List.not_mem_nil,not_false_eq_true,eq_self,and_self,ite_true,first]
     constructor
     · exact Or.inl
     · intro take
       rcases take with accepted | rfl
       · exact accepted
       · cases CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node v) <;> trivial
   · simp only [first,CommonNominalFullDemand.MaskedProbeStep,eq,false_and,ite_false,ih,or_assoc,or_self]

theorem masked_equiv (xs ys : List (Nat × Ty)) (agree : ∀ label, first label xs = first label ys)
 (depth : Nat) (env : Environment Row)
 (order : CommonNominalFullDemand.Ty Row → CommonNominalFullDemand.Ty Row → Prop)
 (obs : Observation Row) :
 MaskedProbeStep Common.rowLe env order [] (finite depth xs) obs ↔
 MaskedProbeStep Common.rowLe env order [] (finite depth ys) obs := by
 cases obs with
 | field label obs => rw [fieldStep,fieldStep,agree]
 | optional label obs => rw [optStep,optStep,agree]
 | _ => cases xs <;> cases ys <;> rfl

theorem checked (xs ys : List (Nat × Ty)) (agree : ∀ label, first label xs = first label ys) :
 Equivalent (recordValues xs) (recordValues ys) := by
 constructor <;> intro depth <;> rw [observed,observed] <;>
   apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
 all_goals
  intro rank env obs got
  cases rank with
  | zero => first | exact (masked_equiv xs ys agree depth env _ obs).mp got | exact (masked_equiv xs ys agree depth env _ obs).mpr got
  | succ n => first | exact (masked_equiv xs ys agree depth env _ obs).mp got | exact (masked_equiv xs ys agree depth env _ obs).mpr got

end Yulang.GeneralRebaseRecordOverwrite271
