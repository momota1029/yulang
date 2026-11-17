import Yulang.GeneralNominalRebaseProjection241
import Yulang.GeneralNominalRebaseStore241
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseOwner241
open GeneralNominalRebaseStore241 (Owner Store Block replace)
open GeneralNominalRebaseProjection241
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDeclarations

variable (baseAtoms : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (checks : Assignment → Prop)
def Retained (model : Assignment) : Prop :=
 PresenceNormalForm.All CommonNominalFullCarrier.model model baseAtoms ∧
 (∀ other ∈ owners, other ≠ owner → PresenceNormalForm.All CommonNominalFullCarrier.model model (store other)) ∧
 checks model

theorem retained_supported
 (baseSupport : ∀ atom ∈ baseAtoms, ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool)
 (otherSupport : ∀ other ∈ owners, other ≠ owner → ∀ atom ∈ store other,
   ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool)
 (checksSupport : RetainedSupported pool checks) :
 RetainedSupported pool (Retained baseAtoms owners store owner checks) := by
 intro first last same
 unfold Retained
 apply and_congr ((atoms_supported baseAtoms baseSupport) first last same)
 apply and_congr ?_ (checksSupport first last same)
 apply forall_congr'; intro other
 apply forall_congr'; intro present
 apply forall_congr'; intro different
 exact atoms_supported (store other) (otherSupport other present different) first last same

variable (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (bindings : GeneralNominalAllocation.Bindings) (actual : Nat → Nat)

theorem projected_store_iff
 (present : owner ∈ owners)
 (baseSupport : ∀ atom ∈ baseAtoms, ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool)
 (otherSupport : ∀ other ∈ owners, other ≠ owner → ∀ atom ∈ store other,
   ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool)
 (checksSupport : RetainedSupported pool checks)
 (isolated : GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id bindings declaration.inputNames pool)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool)
 (centers : ∀ name ∈ declaration.inputNames, actual name ∈ pool)
 (nonempty : ∀ name ∈ declaration.inputNames, GeneralNominalAllocation.occurrences bindings name ≠ [])
 (model : Assignment) :
 (∃ extension : Assignment, Agree pool extension model ∧
   GeneralNominalRebaseStore241.Models baseAtoms owners
     (replace store owner (GeneralNominalAllocation.merges state registry root declaration bindings)) extension ∧
   checks extension ∧ CapturedFits state registry root declaration bindings actual extension) ↔
 Retained baseAtoms owners store owner checks model ∧ SourceFits declaration bindings actual model := by
 have core := projected_iff state registry root declaration bindings actual
   (Retained baseAtoms owners store owner checks)
   (retained_supported baseAtoms owners store owner checks baseSupport otherSupport checksSupport)
   isolated linked centers nonempty model
 rw [← core]
 apply exists_congr; intro extension
 rw [GeneralNominalRebaseStore241.models_replace_iff present]
 unfold Retained
 constructor
 · rintro ⟨same,⟨base,definitions,others⟩,kept,fits⟩
   exact ⟨same,⟨base,others,kept⟩,definitions,fits⟩
 · rintro ⟨same,⟨base,others,kept⟩,definitions,fits⟩
   exact ⟨same,⟨base,definitions,others⟩,kept,fits⟩
end Yulang.GeneralNominalRebaseOwner241
