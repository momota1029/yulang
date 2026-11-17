import Yulang.GeneralNominalRebaseDefinitions241
import Yulang.GeneralNominalCenteredFrame179
set_option backward.isDefEq.respectTransparency false
/-! Exact existential projection for non-escaping stable merge definitions.
Actual-center Fits remain part of the contract. Protected-support and external
endpoint hypotheses are explicit; no operational journal closure is asserted. -/
namespace Yulang.GeneralNominalRebaseProjection241
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCaptureMerges (Fits)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRebaseDefinitions241

variable (state : GeneralNominalState.State) (registry : Registry)
 (root : Nat) (declaration : Declaration) (bindings : Bindings)
 (actual : Nat → Nat)

def SourceFits (model : Assignment) : Prop :=
 ∀ name ∈ declaration.inputNames, ∀ bounds ∈ occurrences bindings name,
 Fits model bounds (model (actual name)).1

def CapturedFits (model : Assignment) : Prop :=
 ∀ name ∈ declaration.inputNames,
 Fits model ((capture state registry root declaration.id bindings).inputs name) (model (actual name)).1

def RetainedSupported (pool : List Nat) (retained : Assignment → Prop) : Prop :=
 ∀ first last, Agree pool first last → (retained first ↔ retained last)

variable {pool : List Nat} {first last : Assignment}

theorem source_fits_congr
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool)
 (centers : ∀ name ∈ declaration.inputNames, actual name ∈ pool)
 (same : Agree pool first last) :
 SourceFits declaration bindings actual first ↔ SourceFits declaration bindings actual last := by
 unfold SourceFits
 apply forall_congr'; intro name
 apply forall_congr'; intro named
 apply forall_congr'; intro bounds
 apply forall_congr'; intro present
 have endpoints := GeneralNominalAllocationSupport.occurrences_endpoints linked name bounds present
 unfold Fits
 rw [same bounds.1 endpoints.1,same bounds.2 endpoints.2,same (actual name) (centers name named)]

theorem captured_iff
 (nonempty : ∀ name ∈ declaration.inputNames, occurrences bindings name ≠ [])
 (model : Assignment)
 (definitions : PresenceNormalForm.All CommonNominalFullCarrier.model model
   (merges state registry root declaration bindings)) :
 CapturedFits state registry root declaration bindings actual model ↔
 SourceFits declaration bindings actual model := by
 unfold CapturedFits SourceFits
 apply forall_congr'; intro name
 apply forall_congr'; intro named
 exact GeneralNominalCaptureMerges.capture_interval_exact state registry root declaration bindings model
   definitions name named (nonempty name named) (model (actual name)).1

/-- The extension may change aggregate cells but fixes all protected values.
Cross constraints and self-checks can be included in retained when their support
is protected. This theorem does not discard their obligations. -/
theorem projected_iff (retained : Assignment → Prop)
 (supported : RetainedSupported pool retained)
 (isolated : Fresh state.seed root declaration.id bindings declaration.inputNames pool)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool)
 (centers : ∀ name ∈ declaration.inputNames, actual name ∈ pool)
 (nonempty : ∀ name ∈ declaration.inputNames, occurrences bindings name ≠ [])
 (model : Assignment) :
 (∃ extension : Assignment, Agree pool extension model ∧ retained extension ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model extension
     (merges state registry root declaration bindings) ∧
   CapturedFits state registry root declaration bindings actual extension) ↔
 retained model ∧ SourceFits declaration bindings actual model := by
 constructor
 · rintro ⟨extension,same,kept,definitions,fits⟩
   refine ⟨(supported extension model same).mp kept,?_⟩
   exact (source_fits_congr declaration bindings actual linked centers same).mp
     ((captured_iff state registry root declaration bindings actual nonempty extension definitions).mp fits)
 · rintro ⟨kept,fits⟩
   let extension := patch state.seed root declaration.id bindings declaration.inputNames model
   have same : Agree pool extension model := preserves _ _ _ _ _ isolated
   have definitions := GeneralNominalRebaseDefinitions241.merges state registry root declaration bindings model isolated linked
   refine ⟨extension,same,(supported extension model same).mpr kept,definitions,?_⟩
   apply (captured_iff state registry root declaration bindings actual nonempty extension definitions).mpr
   exact (source_fits_congr declaration bindings actual linked centers same).mpr fits

theorem atoms_supported (atoms : List (PresenceNormalForm.Atom Nat))
 (supports : ∀ atom ∈ atoms, ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool) :
 RetainedSupported pool (fun model => PresenceNormalForm.All CommonNominalFullCarrier.model model atoms) := by
 intro first last same
 apply forall_congr'; intro atom
 apply forall_congr'; intro present
 exact GeneralNominalCenteredModelExtension.atom_same atom (fun name member => same name (supports atom present name member))

theorem raw_supported (raw : GeneralNominalState.State)
 (supports : ∀ name ∈ GeneralNominalState.sources raw, name ∈ pool) :
 RetainedSupported pool (GeneralNominalState.Models raw) := by
 intro first last same
 exact ⟨GeneralNominalCenteredModelExtension.source_models_same raw (fun name member => same name (supports name member)),
   GeneralNominalCenteredModelExtension.source_models_same raw (fun name member => (same name (supports name member)).symm)⟩

theorem and_supported {one two : Assignment → Prop}
 (first : RetainedSupported pool one) (last : RetainedSupported pool two) :
 RetainedSupported pool (fun model => one model ∧ two model) :=
 fun a b same => and_congr (first a b same) (last a b same)

/-- Specialization retaining an actual raw model and every supplied public atom.
The atoms may contain compatibility and self-check constraints; their finite
support is checked explicitly, not deleted along with merge definitions. -/
theorem constrained_projection (raw : GeneralNominalState.State)
 (atoms : List (PresenceNormalForm.Atom Nat))
 (rawSupport : ∀ name ∈ GeneralNominalState.sources raw, name ∈ pool)
 (atomSupport : ∀ atom ∈ atoms, ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool)
 (isolated : Fresh state.seed root declaration.id bindings declaration.inputNames pool)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool)
 (centers : ∀ name ∈ declaration.inputNames, actual name ∈ pool)
 (nonempty : ∀ name ∈ declaration.inputNames, occurrences bindings name ≠ [])
 (model : Assignment) :
 (∃ extension : Assignment, Agree pool extension model ∧
   (GeneralNominalState.Models raw extension ∧ PresenceNormalForm.All CommonNominalFullCarrier.model extension atoms) ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model extension
     (merges state registry root declaration bindings) ∧
   CapturedFits state registry root declaration bindings actual extension) ↔
 (GeneralNominalState.Models raw model ∧ PresenceNormalForm.All CommonNominalFullCarrier.model model atoms) ∧
   SourceFits declaration bindings actual model :=
 projected_iff state registry root declaration bindings actual _
   (and_supported (raw_supported raw rawSupport) (atoms_supported atoms atomSupport))
   isolated linked centers nonempty model

end Yulang.GeneralNominalRebaseProjection241
