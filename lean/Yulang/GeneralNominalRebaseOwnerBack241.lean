import Yulang.GeneralNominalRebaseOwner241
import Yulang.GeneralNominalRebaseBackExtension241
set_option backward.isDefEq.respectTransparency false
/-! A checked owner replacement has an old-table model extension, fixing its
protected values and retaining every other owner. The interval and support
premises are explicit; no unrestricted journal back-extension is asserted. -/
namespace Yulang.GeneralNominalRebaseOwnerBack241
open GeneralNominalRebaseStore241 (Owner Store Block replace)
open GeneralNominalRebaseOwner241
open GeneralNominalRebaseProjection241
open GeneralNominalRebaseBackExtension241
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDeclarations GeneralNominalAllocation

variable (baseAtoms : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (checks : Assignment → Prop)
 (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (oldBindings newBindings : Bindings) (actual : Nat → Nat)

theorem replaced_back
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
 (model : Assignment)
 (newStore : GeneralNominalRebaseStore241.Models baseAtoms owners
   (replace store owner (merges state registry root declaration newBindings)) model)
 (kept : checks model)
 (fits : CapturedFits state registry root declaration newBindings actual model)
 (refinement : Refines declaration oldBindings newBindings model) :
 ∃ extension : Assignment, Agree pool extension model ∧
 GeneralNominalRebaseStore241.Models baseAtoms owners store extension ∧
 checks extension ∧ CapturedFits state registry root declaration oldBindings actual extension := by
 obtain ⟨base,newDefinitions,others⟩ := (GeneralNominalRebaseStore241.models_replace_iff present).mp newStore
 have retained : Retained baseAtoms owners store owner checks model := ⟨base,others,kept⟩
 obtain ⟨extension,same,⟨oldBase,oldOthers,oldChecks⟩,oldDefinitions,oldFits⟩ :=
   back_extension declaration oldBindings newBindings actual model state registry root
     (Retained baseAtoms owners store owner checks)
     (retained_supported baseAtoms owners store owner checks baseSupport otherSupport checksSupport)
     isolated linked centers oldNonempty newNonempty retained newDefinitions fits refinement
 refine ⟨extension,same,?_,oldChecks,oldFits⟩
 have replaced : GeneralNominalRebaseStore241.Models baseAtoms owners
     (replace store owner (merges state registry root declaration oldBindings)) extension :=
   (GeneralNominalRebaseStore241.models_replace_iff present).mpr ⟨oldBase,oldDefinitions,oldOthers⟩
 rw [← oldBlock,GeneralNominalRebaseStore241.replace_current] at replaced
 exact replaced
end Yulang.GeneralNominalRebaseOwnerBack241
