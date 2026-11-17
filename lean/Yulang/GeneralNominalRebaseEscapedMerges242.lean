import Yulang.GeneralNominalRebaseEscapedStore242
set_option backward.isDefEq.respectTransparency false
/-! Structural producers for actual stable merge entries. The multiplicity
condition excludes a newly private cell absent from the old target set. -/
namespace Yulang.GeneralNominalRebaseEscapedMerges242
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalRebaseDefinitions241
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebaseEscapedStore242
open GeneralNominalRebaseStore241 (Owner Store Block Models)
open GeneralNominalCommonBridge (Assignment)

theorem external_entries (seed root declaration : Nat) (bindings : Bindings) (names : List Nat)
 (fresh : Fresh seed root declaration bindings names pool)
 (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) :
 External (entries seed root declaration bindings names) := by
 intro entry member name present target included equal
 have source := supported seed root declaration bindings names linked entry member name present
 have absent := entries_fresh seed root declaration bindings names fresh target included
 exact absent (equal.symm ▸ source)

theorem targets_within (seed root declaration : Nat) (oldBindings newBindings : Bindings)
 (names : List Nat)
 (multiplicity : ∀ name ∈ names, (occurrences newBindings name).length ≠ 1 →
   (occurrences oldBindings name).length ≠ 1) :
 TargetsWithin (entries seed root declaration newBindings names)
   (entries seed root declaration oldBindings names) := by
 intro entry member
 obtain ⟨name,named,many,rfl | rfl⟩ := (member_iff seed root declaration newBindings names).mp member
 · refine ⟨(slot seed root declaration 0 name oldBindings,lower (occurrences oldBindings name)),?_,rfl⟩
   exact (member_iff seed root declaration oldBindings names).mpr
     ⟨name,named,multiplicity name named many,Or.inl rfl⟩
 · refine ⟨(slot seed root declaration 1 name oldBindings,upper (occurrences oldBindings name)),?_,rfl⟩
   exact (member_iff seed root declaration oldBindings names).mpr
     ⟨name,named,multiplicity name named many,Or.inr rfl⟩

theorem definition_block_eq (state : GeneralNominalState.State) (registry : Registry)
 (root : Nat) (declaration : Declaration) (bindings : Bindings) :
 definitionBlock (entries state.seed root declaration.id bindings declaration.inputNames) =
 GeneralNominalAllocation.merges state registry root declaration bindings := by
 unfold definitionBlock entries GeneralNominalAllocation.merges
 rw [List.flatMap_assoc]
 apply congrArg (fun f => declaration.inputNames.flatMap f)
 funext name
 cases found : occurrences bindings name with
 | nil => simp [found,capture,GeneralNominalAllocation.source,slot]
 | cons head tail =>
   cases tail with
   | nil => simp
   | cons second rest => simp [found,capture,GeneralNominalAllocation.source,slot]

theorem actual_projection_iff (base : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (oldBindings newBindings : Bindings)
 (present : owner ∈ owners)
 (oldBlock : store owner = GeneralNominalAllocation.merges state registry root declaration oldBindings)
 (oldFresh : Fresh state.seed root declaration.id oldBindings declaration.inputNames pool)
 (newFresh : Fresh state.seed root declaration.id newBindings declaration.inputNames pool)
 (oldLinked : GeneralNominalAllocationSupport.Endpoints oldBindings pool)
 (newLinked : GeneralNominalAllocationSupport.Endpoints newBindings pool)
 (multiplicity : ∀ name ∈ declaration.inputNames, (occurrences newBindings name).length ≠ 1 →
   (occurrences oldBindings name).length ≠ 1) (model : Assignment) :
 (∃ old, Preserves (entries state.seed root declaration.id oldBindings declaration.inputNames) old model ∧
   Models base owners store old) ↔
 (∃ next, Preserves (entries state.seed root declaration.id oldBindings declaration.inputNames) next model ∧
   Models (inline (entries state.seed root declaration.id oldBindings declaration.inputNames) base) owners
     (replaceAll store owner (entries state.seed root declaration.id oldBindings declaration.inputNames)
       (entries state.seed root declaration.id newBindings declaration.inputNames)) next) := by
 apply projection_iff base owners store owner _ _ present
 · exact oldBlock.trans (definition_block_eq state registry root declaration oldBindings).symm
 · exact coherent state.seed root declaration.id oldBindings declaration.inputNames
 · exact external_entries _ _ _ _ _ oldFresh oldLinked
 · exact coherent state.seed root declaration.id newBindings declaration.inputNames
 · exact external_entries _ _ _ _ _ newFresh newLinked
 · exact targets_within _ _ _ _ _ _ multiplicity
end Yulang.GeneralNominalRebaseEscapedMerges242
