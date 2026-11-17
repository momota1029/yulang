import Yulang.GeneralNominalOrderedSupport248
import Yulang.GeneralNominalRebaseDefinitions241
import Yulang.GeneralPresenceOrderedPrepared247
/-! Executable ordered preparation of the actual stable merge entries. Coherence
and RHS support come from the real Definitions241/AllocationSupport theorems.
The protected-pool Fresh condition is explicit; it is not inferred for arbitrary
reused owners from the weaker versioned allocator Fresh predicate. -/
namespace Yulang.GeneralNominalOrderedMerge248
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalAllocation (Bindings occurrences lower upper)
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDedup247
open GeneralPresenceOrderedPrepared247 GeneralPresenceOrderedSort247
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralNominalCommonBridge (Assignment)

abbrev entries := GeneralNominalRebaseDefinitions241.entries

theorem coherent (seed root declaration : Nat) (bindings : Bindings) (names : List Nat) :
 GeneralPresenceOwnerRewrite244.Coherent (entries seed root declaration bindings names) :=
 GeneralNominalRebaseDefinitions241.coherent seed root declaration bindings names

theorem typed_supported (seed root declaration : Nat) (bindings : Bindings) (names pool : List Nat)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) :
 ∀ rhs ∈ entries seed root declaration bindings names, ∀ name ∈ typedReads rhs.2, name ∈ pool := by
 intro rhs member name read
 exact GeneralNominalRebaseDefinitions241.supported seed root declaration bindings names linked rhs member name
   (GeneralNominalOrderedSupport248.typed_reads_subset rhs.2 read)

theorem prepared (seed root declaration : Nat) (bindings : Bindings) (names pool : List Nat)
 (fresh : GeneralNominalRebaseDefinitions241.Fresh seed root declaration bindings names pool)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) :
 ∃ sorted, prepare (entries seed root declaration bindings names) = some sorted ∧ SafeOrder sorted := by
 apply prepare_complete (fun _ => 0)
 intro rhs member target present read
 have inPool := typed_supported seed root declaration bindings names pool linked rhs member target.1 read
 exact False.elim ((GeneralNominalRebaseDefinitions241.entries_fresh seed root declaration bindings names fresh target present) inPool)

theorem original_extension (seed root declaration : Nat) (bindings : Bindings) (names pool : List Nat)
 (fresh : GeneralNominalRebaseDefinitions241.Fresh seed root declaration bindings names pool)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) (assignment : Assignment) :
 ∃ sorted extended,
   prepare (entries seed root declaration bindings names) = some sorted ∧
   extended = solve CommonNominalFullCarrier.model sorted assignment ∧
   All CommonNominalFullCarrier.model extended (GeneralPresenceDefinitionRewrite244.block (entries seed root declaration bindings names)) ∧
   (∀ name ∈ pool, extended name = assignment name) ∧
   (∀ name, (extended name).2 = (assignment name).2) := by
 obtain ⟨sorted,success,_⟩ := prepared seed root declaration bindings names pool fresh linked
 obtain ⟨valid,outside,rows⟩ := prepared_extension CommonNominalFullCarrier.model
   (fun value => CommonNominalFullCarrier.subtype_refl value) (entries seed root declaration bindings names) sorted
   (coherent seed root declaration bindings names) success assignment
 refine ⟨sorted,solve CommonNominalFullCarrier.model sorted assignment,success,rfl,valid,?_,rows⟩
 intro name member
 apply outside name
 intro entry present equal
 exact GeneralNominalRebaseDefinitions241.entries_fresh seed root declaration bindings names fresh entry present (equal ▸ member)

theorem merges_of_entries (state : GeneralNominalState.State) (registry : GeneralDeclarations.Registry)
 (root : Nat) (declaration : GeneralDeclarations.Declaration) (bindings : Bindings) (assignment : Assignment)
 (valid : All CommonNominalFullCarrier.model assignment
   (GeneralPresenceDefinitionRewrite244.block (entries state.seed root declaration.id bindings declaration.inputNames))) :
 All CommonNominalFullCarrier.model assignment (GeneralNominalAllocation.merges state registry root declaration bindings) := by
 intro atom member
 obtain ⟨name,named,member⟩ := List.mem_flatMap.mp member
 have produce (many : (occurrences bindings name).length ≠ 1) :
     All CommonNominalFullCarrier.model assignment
       (GeneralNominalAllocation.equations (GeneralNominalRebaseDefinitions241.slot state.seed root declaration.id 0 name bindings) (lower (occurrences bindings name)) ++
        GeneralNominalAllocation.equations (GeneralNominalRebaseDefinitions241.slot state.seed root declaration.id 1 name bindings) (upper (occurrences bindings name))) := by
   apply (all_append ..).mpr
   constructor
   · intro part present
     exact valid part (List.mem_flatMap.mpr ⟨_,(GeneralNominalRebaseDefinitions241.member_iff ..).mpr
       ⟨name,named,many,Or.inl rfl⟩,present⟩)
   · intro part present
     exact valid part (List.mem_flatMap.mpr ⟨_,(GeneralNominalRebaseDefinitions241.member_iff ..).mpr
       ⟨name,named,many,Or.inr rfl⟩,present⟩)
 cases found : occurrences bindings name with
 | nil => exact produce (by simp [found]) atom (by simpa [found,GeneralNominalAllocation.capture,GeneralNominalAllocation.source,GeneralNominalRebaseDefinitions241.slot] using member)
 | cons first rest =>
   cases rest with
   | nil => simp [found] at member
   | cons second tail => exact produce (by simp [found]) atom (by simpa [found,GeneralNominalAllocation.capture,GeneralNominalAllocation.source,GeneralNominalRebaseDefinitions241.slot] using member)

theorem actual_merge_extension (state : GeneralNominalState.State) (registry : GeneralDeclarations.Registry)
 (root : Nat) (declaration : GeneralDeclarations.Declaration) (bindings : Bindings) (pool : List Nat)
 (fresh : GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id bindings declaration.inputNames pool)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) (assignment : Assignment) :
 ∃ extended, All CommonNominalFullCarrier.model extended (GeneralNominalAllocation.merges state registry root declaration bindings) ∧
   (∀ name ∈ pool, extended name = assignment name) ∧
   (∀ name, (extended name).2 = (assignment name).2) := by
 obtain ⟨_,extended,_,_,valid,kept,rows⟩ := original_extension state.seed root declaration.id bindings declaration.inputNames pool fresh linked assignment
 exact ⟨extended,merges_of_entries state registry root declaration bindings extended valid,kept,rows⟩
end Yulang.GeneralNominalOrderedMerge248
