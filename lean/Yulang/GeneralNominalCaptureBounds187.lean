import Yulang.GeneralNominalCaptureMerges
import Yulang.GeneralNominalRecursiveInspection

/-! Recorded merge equations expose the raw-interval criterion. Projection
constraints imply merged Fits for an actual captured value, without assuming it. -/
namespace Yulang.GeneralNominalCaptureBounds187
open GeneralNominalRecursiveInspection GeneralNominalAllocation GeneralDeclarations
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

 theorem occurrence_iff (state : GeneralNominalState.State) (report : Report state)
    (name : Nat) (pair : GeneralSourceState.Interval) :
    pair ∈ occurrences (bindings state report) name ↔
      ∃ captured ∈ report.captures, captured.name = name ∧
        (state.base.source captured.bounds.1, state.base.source captured.bounds.2) = pair := by
  simp only [occurrences,List.mem_map,List.mem_filter,beq_iff_eq,bindings]
  constructor
  · rintro ⟨binding,⟨⟨captured,present,rfl⟩,same⟩,equal⟩
    exact ⟨captured,present,same,equal⟩
  · rintro ⟨captured,present,same,equal⟩
    exact ⟨_,⟨⟨captured,present,rfl⟩,same⟩,equal⟩

 theorem occurrence_nonempty (state : GeneralNominalState.State) (report : Report state)
    (captured : Capture state) (present : captured ∈ report.captures) :
    occurrences (bindings state report) captured.name ≠ [] := by
  have member := (occurrence_iff state report captured.name
    (state.base.source captured.bounds.1,state.base.source captured.bounds.2)).mpr
    ⟨captured,present,rfl,rfl⟩
  intro empty
  rw [empty] at member
  cases member

 theorem merged_iff_raw (state : GeneralNominalState.State) (report : Report state)
    (registry : Registry) (invocation : Nat) (declaration : Declaration)
    (model : Assignment)
    (recorded : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration (bindings state report)))
    (name : Nat) (declared : name ∈ declaration.inputNames)
    (nonempty : occurrences (bindings state report) name ≠ []) (value : Ty) :
    GeneralNominalCaptureMerges.Fits model
      ((capture state registry invocation declaration.id (bindings state report)).inputs name) value ↔
    ∀ captured ∈ report.captures, captured.name = name → Fits state model captured.bounds value := by
  rw [GeneralNominalCaptureMerges.capture_interval_exact state registry invocation declaration
    (bindings state report) model recorded name declared nonempty value]
  constructor
  · intro all captured present same
    exact all _ ((occurrence_iff ..).mpr ⟨captured,present,same,rfl⟩)
  · intro all pair present
    obtain ⟨captured,member,same,rfl⟩ := (occurrence_iff ..).mp present
    exact all captured member same

 theorem projected_merged (state : GeneralNominalState.State) (report : Report state)
    (registry : Registry) (invocation : Nat) (declaration : Declaration)
    (model : Assignment) (projection : ProjectionModels state report model)
    (recorded : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges state registry invocation declaration (bindings state report)))
    (captured : Capture state) (present : captured ∈ report.captures)
    (declared : captured.name ∈ declaration.inputNames)
    (origin : GeneralNominalRecursiveInspection.Origin) (source : captured.origin = some origin)
    (value : Ty) (seen : Observes model origin value) :
    GeneralNominalCaptureMerges.Fits model
      ((capture state registry invocation declaration.id (bindings state report)).inputs captured.name) value := by
  apply (merged_iff_raw state report registry invocation declaration model recorded captured.name
    declared (occurrence_nonempty state report captured present) value).mpr
  intro last member same
  exact projected_capture_sound state report model projection captured last present member same.symm
    origin source value seen

 theorem fits_equivalent (model : Assignment) (bounds : GeneralSourceState.Interval)
    (one two : Ty) (same : Equivalent one two) :
    GeneralNominalCaptureMerges.Fits model bounds one ↔ GeneralNominalCaptureMerges.Fits model bounds two := by
  constructor
  · intro fits; exact ⟨subtype_trans fits.1 same.1,subtype_trans same.2 fits.2⟩
  · intro fits; exact ⟨subtype_trans fits.1 same.2,subtype_trans same.1 fits.2⟩

end Yulang.GeneralNominalCaptureBounds187
