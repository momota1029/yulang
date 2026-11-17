import Yulang.GeneralNominalCommonBridge
import Yulang.CommonNominalFullConstructors
set_option backward.isDefEq.respectTransparency false
/-! Full nominal assignment congruence. Rows are literal, types semantic. -/
namespace Yulang.GeneralNominalAssignmentCongruence238
open CommonNominalFullCarrier
open Core.PresenceGeneration (Comp TyTerm RowTerm)
def Same (first last : α → Comp model) : Prop :=
 ∀ n, Equivalent (first n).1 (last n).1 ∧ (first n).2 = (last n).2

theorem refl (first : α → Comp model) : Same first first :=
 fun _ => ⟨⟨subtype_refl _,subtype_refl _⟩,rfl⟩
theorem symm (same : Same (α := α) first last) : Same last first :=
 fun n => ⟨⟨(same n).1.2,(same n).1.1⟩,(same n).2.symm⟩
theorem subtype_iff (a : Equivalent first first') (b : Equivalent last last') :
 Subtype first last ↔ Subtype first' last' :=
 ⟨fun h => subtype_trans a.2 (subtype_trans h b.1),
  fun h => subtype_trans a.1 (subtype_trans h b.2)⟩
theorem row_eval (same : Same (α := α) first last) (term : RowTerm α) :
 term.eval model first = term.eval model last := by
 induction term with
 | var n => exact (same n).2
 | empty => rfl
 | join _ _ a b => simp only [RowTerm.eval,a,b]

theorem default_mono (label : Nat) (a : Subtype first last) (b : Subtype fallback replacement) :
 Subtype (recordDefault label first fallback) (recordDefault label last replacement) := by
 intro depth
 cases depth with
 | zero => exact CommonNominalFullDemand.producerLe_record_mono label (CommonNominalFullDemand.producerLe_refl _) (a 0)
 | succ depth => exact CommonNominalFullDemand.producerLe_recordDefault label (a (depth+1)) (quote_observe_le b (depth+1))

theorem type_eval (same : Same (α := α) first last) (term : TyTerm α) :
 Equivalent (term.eval model first) (term.eval model last) := by
 induction term with
 | var n => exact (same n).1
 | base | bottom | top | emptyRecord | exactEmpty => exact ⟨subtype_refl _,subtype_refl _⟩
 | union _ _ a b => exact ⟨common_union_mono a.1 b.1,common_union_mono a.2 b.2⟩
 | inter _ _ a b => exact ⟨common_inter_mono a.1 b.1,common_inter_mono a.2 b.2⟩
 | pair _ _ a b => exact ⟨(common_pair_iff ..).mpr ⟨a.1,b.1⟩,(common_pair_iff ..).mpr ⟨a.2,b.2⟩⟩
 | required label _ a => exact ⟨common_record_mono label a.1 (subtype_refl _),common_record_mono label a.2 (subtype_refl _)⟩
 | record label _ _ a b => exact ⟨common_record_mono label a.1 b.1,common_record_mono label a.2 b.2⟩
 | recordDefault label _ _ a b => exact ⟨default_mono label a.1 b.1,default_mono label a.2 b.2⟩
 | variant label _ a => exact ⟨(common_variant_iff label ..).mpr a.1,(common_variant_iff label ..).mpr a.2⟩
 | arrow input incoming output outgoing a b =>
   change Equivalent (arrow _ (incoming.eval model first) _ (outgoing.eval model first))
     (arrow _ (incoming.eval model last) _ (outgoing.eval model last))
   rw [row_eval same incoming,row_eval same outgoing]
   exact ⟨(common_arrow_iff ..).mpr ⟨a.2,Common.rowLe_refl _,b.1,Common.rowLe_refl _⟩,
     (common_arrow_iff ..).mpr ⟨a.1,Common.rowLe_refl _,b.2,Common.rowLe_refl _⟩⟩

theorem atom_iff (same : Same (α := α) first last) (atom : PresenceNormalForm.Atom α) :
 atom.Holds model first ↔ atom.Holds model last := by
 cases atom with
 | tyLe a b => exact subtype_iff (type_eval same a) (type_eval same b)
 | rowLe a b => simp only [PresenceNormalForm.Atom.Holds,row_eval same a,row_eval same b]

theorem all_iff (same : Same (α := α) first last) (atoms : List (PresenceNormalForm.Atom α)) :
 PresenceNormalForm.All model first atoms ↔ PresenceNormalForm.All model last atoms := by
 constructor <;> intro valid atom member
 · exact (atom_iff same atom).mp (valid atom member)
 · exact (atom_iff same atom).mpr (valid atom member)
end Yulang.GeneralNominalAssignmentCongruence238
