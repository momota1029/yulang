import Yulang.GeneralRebaseCompoundReplacementPublic273

set_option maxRecDepth 19000
set_option maxHeartbeats 4600000
namespace Yulang.GeneralRebaseCompoundChildBoundary273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompoundObstruction238 (oldPlan currentPlan old_lower current_lower)
open GeneralDictionaryCompoundPoint238 (point original_plan_retained)
open GeneralNominalVersionedPlans231 (Holds Outputs emittedSchema variables)
open GeneralRebaseCompoundReplacement273 (lower emitted_same shape)
open GeneralRebaseCompoundReplacementFrame273 (Meaning)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

theorem raw_lower_equation (m : Assignment) (p : GeneralNominalCenters.Plan GeneralDictionaryJournalRefinement228Source.roles)
 (schema : emittedSchema p = emittedSchema oldPlan) (valid : Outputs p m) :
 Equivalent (m lower).1 (variant 0 (variables p m .lower 0)) := by
 unfold Outputs at valid
 rw [schema,GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema] at valid
 exact valid _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem operand (m : Assignment) (p : GeneralNominalCenters.Plan GeneralDictionaryJournalRefinement228Source.roles)
 (decl : p.packet.declaration = GeneralDictionaryCompoundSource238.declaration) :
 variables p m .lower 0 =
 (m ((GeneralNominalVersionedFrame231.capture p.packet).inputs 0).1).1 := by
 unfold variables
 rw [decl]
 rfl

theorem variant_equivalent (first last : Ty) (same : Equivalent first last) :
 Equivalent (variant 0 first) (variant 0 last) :=
 ⟨(common_variant_iff ..).mpr same.1,(common_variant_iff ..).mpr same.2⟩

theorem historical_lower (m : Assignment) (valid : Models point m) :
 Equivalent (m lower).1 (variant 0 GeneralDictionaryOptionalOutput229.value) := by
 have packet := valid.2.1 oldPlan original_plan_retained
 have lowerEq := raw_lower_equation m oldPlan rfl packet.2.2
 rw [operand m oldPlan rfl] at lowerEq
 exact equivalent_trans lowerEq (variant_equivalent _ _ (equivalent_trans (old_lower m packet)
   (GeneralDictionaryCompoundObstruction238.associated_value m packet)))

theorem replacement_lower (m : Assignment) (valid : Meaning m) :
 Equivalent (m lower).1 shape := by
 have packet := valid.1
 have lowerEq := raw_lower_equation m currentPlan emitted_same packet.2.2
 rw [operand m currentPlan rfl] at lowerEq
 have source := (GeneralRebaseCompoundReplacementFrame273.snapshot_exact m).mp packet.1
 exact equivalent_trans lowerEq (variant_equivalent _ _ (equivalent_trans (current_lower m packet)
   (GeneralDictionaryJournalRefinement228Source.width_two m source.1)))

theorem cannot_fix_child_lower (historical replacement : Assignment)
 (old : Models point historical) (fresh : Meaning replacement) :
 ¬ Equivalent (historical lower).1 (replacement lower).1 := by
 intro same
 have left := historical_lower historical old
 have right := replacement_lower replacement fresh
 have compound := equivalent_trans ⟨left.2,left.1⟩ (equivalent_trans same right)
 exact GeneralDictionaryOptionalOutput229.not_width
   ⟨(common_variant_iff ..).mp compound.1,(common_variant_iff ..).mp compound.2⟩

/-- The projection-preserving replacement changes a real generated child
coordinate, even up to semantic equivalence. It cannot preserve a stronger
projection that includes that lower cell. -/
theorem larger_projection_has_no_replacement (historical : Assignment)
 (old : Models point historical) :
 ¬ ∃ replacement, GeneralRebaseCompoundRows273.Agrees replacement historical ∧
   Equivalent (replacement lower).1 (historical lower).1 ∧ Meaning replacement := by
 rintro ⟨replacement,_,same,valid⟩
 exact cannot_fix_child_lower historical replacement old valid ⟨same.2,same.1⟩

end Yulang.GeneralRebaseCompoundChildBoundary273
