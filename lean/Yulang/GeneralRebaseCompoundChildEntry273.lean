import Yulang.GeneralRebaseCompoundPairedCompletion273
import Yulang.GeneralRebaseCompoundReplacementEvidence273

set_option maxRecDepth 20000
set_option maxHeartbeats 4900000
namespace Yulang.GeneralRebaseCompoundChildEntry273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedCycles232 (Head)
open GeneralNominalRecursiveInspection (Test Observes)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralRebaseCompoundReplacement273 (lower upper shape center)
open GeneralRebaseCompoundReplacementFrame273 (Meaning)
open GeneralDictionaryInspectionHeads215 (Tagged tagged_test tagged_equivalent tag_subtype)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

theorem generated_linked :
 lower ∈ GeneralNominalState.sources point.core.erased.current.context.state ∧
 upper ∈ GeneralNominalState.sources point.core.erased.current.context.state := by decide +kernel

theorem missing_lower (slot : Fin point.core.erased.current.context.state.base.slots) :
 point.core.erased.current.context.state.base.source slot ≠ lower := by
 intro same
 have small : slot.val < 5 := slot.isLt
 have exposed : slot.val = lower := same
 have high : 4 < lower := GeneralDictionaryCompoundPacket238.fresh_large 3
 omega

theorem missing_upper (slot : Fin point.core.erased.current.context.state.base.slots) :
 point.core.erased.current.context.state.base.source slot ≠ upper := by
 intro same
 have small : slot.val < 5 := slot.isLt
 have exposed : slot.val = upper := same
 have high : 4 < upper := GeneralDictionaryCompoundPacket238.fresh_large 4
 omega

theorem no_lower_slot : sourceSlot point.core.erased.current.context.state.base lower = none := by
 cases found : sourceSlot point.core.erased.current.context.state.base lower with
 | none => rfl
 | some slot => exact False.elim (missing_lower slot ((sourceSlot_exact ..).mp found))

theorem no_upper_slot : sourceSlot point.core.erased.current.context.state.base upper = none := by
 cases found : sourceSlot point.core.erased.current.context.state.base upper with
 | none => rfl
 | some slot => exact False.elim (missing_upper slot ((sourceSlot_exact ..).mp found))

/-- Liveness/reservation of the emitted identity is not location in the base
slot map. Changing only a model or either endpoint's type cannot change lookup. -/
theorem linked_but_unlocated :
 lower ∈ GeneralNominalState.sources point.core.erased.current.context.state ∧
 upper ∈ GeneralNominalState.sources point.core.erased.current.context.state ∧
 GeneralNominalRecursiveCandidates.arguments point.core.erased.current.context
   (GeneralNominalVersionedCandidates231.inputs childSite.occurrence) = none :=
 ⟨generated_linked.1,generated_linked.2,GeneralDictionaryCompoundChildPending238.unlocated⟩

def requiredSources : List Nat := [0,1,2,3,4,lower,upper]

theorem required_distinct : requiredSources.Nodup := by decide +kernel

/-- A raw registration that keeps all five original addresses and preserves
both actual generated names needs at least seven slots. Merely making the
two endpoint types equal does not identify their source coordinates. -/
theorem registration_slot_bound (raw : GeneralSourceState.State)
 (contains : ∀ name ∈ requiredSources, ∃ slot, raw.source slot = name) :
 7 ≤ raw.slots := by
 have inside : requiredSources ⊆ List.ofFn raw.source := by
   intro id visible
   obtain ⟨slot,same⟩ := contains id visible
   exact List.mem_ofFn.mpr ⟨slot,same⟩
 have sizes := required_distinct.length_le_of_subset inside
 simpa only [requiredSources,List.length_cons,List.length_nil,List.length_ofFn] using sizes

theorem shape_head : (Test.structural (.variant 0)).Holds shape :=
 ⟨[.emptyRecord],rfl,subtype_refl _,subtype_refl _⟩

theorem point_child_head (m : Assignment) (valid : Meaning m) :
 (Test.structural (.variant 0)).Holds (m lower).1 :=
 (GeneralNominalOriginCongruence238.test_iff
   (GeneralRebaseCompoundChildBoundary273.replacement_lower m valid) _).mpr shape_head

theorem mismatch (t : Ty) (variantHead : (Test.structural (.variant 0)).Holds t) :
 ¬ (Test.nominal 0 2).Holds t := by
 intro nominalHead
 have unequal := tag_subtype (tagged_test _ variantHead) (tagged_test _ nominalHead) (subtype_refl t)
 cases unequal

/-- Even if this generated endpoint were located with its readback preserved,
the sole declaration's nominal head is not a proof of a matching variant.
This is only a semantic head obstruction, not a new V8 diagnostic. -/
theorem no_matching_nominal_head (m : Assignment) (valid : Meaning m) :
 ¬ GeneralNominalOriginTerms.Head m (.source lower) (.nominal 0 2) := by
 intro available
 exact mismatch _ (point_child_head m valid) (available.2 _ (.source _))

end Yulang.GeneralRebaseCompoundChildEntry273
