import Yulang.GeneralNominalRebaseProtectedLive241
namespace Yulang.GeneralNominalRebaseOwnerLive241
open GeneralNominalRebaseStore241 (Owner Store Block replace)
open GeneralNominalRebaseProjection241
open GeneralNominalRebaseBackExtension241
open GeneralNominalRebaseLiveLabels241
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations GeneralNominalAllocation GeneralNominalCenters

variable (baseAtoms : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (checks : Assignment → Prop)
 (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (oldBindings newBindings : Bindings) (actual : Nat → Nat)

def OldModels (model : Assignment) : Prop :=
 GeneralNominalRebaseStore241.Models baseAtoms owners store model ∧ checks model ∧
 CapturedFits state registry root declaration oldBindings actual model

def NewModels (model : Assignment) : Prop :=
 GeneralNominalRebaseStore241.Models baseAtoms owners
   (replace store owner (merges state registry root declaration newBindings)) model ∧ checks model ∧
 CapturedFits state registry root declaration newBindings actual model

variable {roles : Roles.RoleDecls} (sites : List (Site roles)) {pool : List Nat}

theorem back_extension
 (present : owner ∈ owners)
 (oldBlock : store owner = merges state registry root declaration oldBindings)
 (baseSupport : ∀ atom ∈ baseAtoms, ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool)
 (otherSupport : ∀ other ∈ owners, other ≠ owner → ∀ atom ∈ store other,
   ∀ name ∈ GeneralNominalState.atomSources atom, name ∈ pool)
 (checksSupport : RetainedSupported pool checks)
 (isolated : GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id oldBindings declaration.inputNames pool)
 (linked : GeneralNominalAllocationSupport.Endpoints oldBindings pool)
 (centers : ∀ name ∈ declaration.inputNames, actual name ∈ pool)
 (oldNonempty : ∀ name ∈ declaration.inputNames, occurrences oldBindings name ≠ [])
 (newNonempty : ∀ name ∈ declaration.inputNames, occurrences newBindings name ≠ [])
 (liveProtected : ∀ site ∈ sites, ∀ index, site.center index ∈ pool)
 (refinement : ∀ model, NewModels baseAtoms owners store owner checks state registry root declaration newBindings actual model →
   Refines declaration oldBindings newBindings model) :
 BackExtension sites
   (OldModels baseAtoms owners store checks state registry root declaration oldBindings actual)
   (NewModels baseAtoms owners store owner checks state registry root declaration newBindings actual) := by
 apply GeneralNominalRebaseProtectedLive241.back_extension liveProtected
 intro model valid
 obtain ⟨extension,same,oldStore,oldChecks,oldFits⟩ :=
   GeneralNominalRebaseOwnerBack241.replaced_back baseAtoms owners store owner checks state registry root
     declaration oldBindings newBindings actual present oldBlock baseSupport otherSupport checksSupport
     isolated linked centers oldNonempty newNonempty model valid.1 valid.2.1 valid.2.2 (refinement model valid)
 exact ⟨extension,⟨oldStore,oldChecks,oldFits⟩,same⟩

theorem bounded_models
 (extension : BackExtension sites
   (OldModels baseAtoms owners store checks state registry root declaration oldBindings actual)
   (NewModels baseAtoms owners store owner checks state registry root declaration newBindings actual))
 (known : ∀ model, OldModels baseAtoms owners store checks state registry root declaration oldBindings actual model →
   Bounded labelRegistry seed sourceRoot budget semantics sites model) :
 ∀ model, NewModels baseAtoms owners store owner checks state registry root declaration newBindings actual model →
   Bounded labelRegistry seed sourceRoot budget semantics sites model :=
 all_models extension known
end Yulang.GeneralNominalRebaseOwnerLive241
