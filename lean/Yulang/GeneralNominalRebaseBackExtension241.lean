import Yulang.GeneralNominalRebaseProjection241
set_option backward.isDefEq.respectTransparency false
/-! Reconstructed from the preserved theorem summary; requires fresh verification.
Existential old private extension under actual interval refinement. -/
namespace Yulang.GeneralNominalRebaseBackExtension241
open GeneralDeclarations GeneralNominalAllocation CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRebaseProjection241
variable (declaration : Declaration) (oldBindings newBindings : Bindings)
 (actual : Nat → Nat) (model : Assignment)
def Refines : Prop :=
 ∀ name ∈ declaration.inputNames, ∀ oldBounds ∈ occurrences oldBindings name,
 ∃ newBounds ∈ occurrences newBindings name,
   Subtype (model oldBounds.1).1 (model newBounds.1).1 ∧
   Subtype (model newBounds.2).1 (model oldBounds.2).1

theorem source_fits_back
 (refinement : Refines declaration oldBindings newBindings model)
 (newFits : SourceFits declaration newBindings actual model) :
 SourceFits declaration oldBindings actual model := by
 intro name named bounds present
 obtain ⟨next,member,lower,upper⟩ := refinement name named bounds present
 have fits := newFits name named next member
 exact ⟨subtype_trans lower fits.1,subtype_trans fits.2 upper⟩

theorem back_extension_of_source_fits
 (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (retained : Assignment → Prop) {pool : List Nat}
 (supported : RetainedSupported pool retained)
 (isolated : GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id oldBindings declaration.inputNames pool)
 (linked : GeneralNominalAllocationSupport.Endpoints oldBindings pool)
 (centers : ∀ name ∈ declaration.inputNames, actual name ∈ pool)
 (nonempty : ∀ name ∈ declaration.inputNames, occurrences oldBindings name ≠ [])
 (kept : retained model)
 (newFits : SourceFits declaration newBindings actual model)
 (refinement : Refines declaration oldBindings newBindings model) :
 ∃ extension : Assignment, Agree pool extension model ∧ retained extension ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model extension
   (merges state registry root declaration oldBindings) ∧
 CapturedFits state registry root declaration oldBindings actual extension := by
 apply (projected_iff state registry root declaration oldBindings actual retained
   supported isolated linked centers nonempty model).mpr
 exact ⟨kept,source_fits_back declaration oldBindings newBindings actual model refinement newFits⟩

theorem back_extension
 (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (retained : Assignment → Prop) {pool : List Nat}
 (supported : RetainedSupported pool retained)
 (isolated : GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id oldBindings declaration.inputNames pool)
 (linked : GeneralNominalAllocationSupport.Endpoints oldBindings pool)
 (centers : ∀ name ∈ declaration.inputNames, actual name ∈ pool)
 (oldNonempty : ∀ name ∈ declaration.inputNames, occurrences oldBindings name ≠ [])
 (newNonempty : ∀ name ∈ declaration.inputNames, occurrences newBindings name ≠ [])
 (kept : retained model)
 (definitions : PresenceNormalForm.All CommonNominalFullCarrier.model model
   (merges state registry root declaration newBindings))
 (newFits : CapturedFits state registry root declaration newBindings actual model)
 (refinement : Refines declaration oldBindings newBindings model) :
 ∃ extension : Assignment, Agree pool extension model ∧ retained extension ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model extension
   (merges state registry root declaration oldBindings) ∧
 CapturedFits state registry root declaration oldBindings actual extension :=
 back_extension_of_source_fits declaration oldBindings newBindings actual model state registry root
 retained supported isolated linked centers oldNonempty kept
 ((captured_iff state registry root declaration newBindings actual newNonempty model definitions).mp newFits)
 refinement
end Yulang.GeneralNominalRebaseBackExtension241
