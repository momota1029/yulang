import Yulang.GeneralNominalOrderedRawExpansion249
import Yulang.GeneralNominalRebaseViewSubst243

/-! Old targets are eliminated from typed support of a rewritten actual raw
view. Row-only references survive intentionally. New target separation remains
a distinct condition when the target domain grows. -/
namespace Yulang.GeneralNominalOrderedViewClosed249
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralNominalRebaseRawView243
open GeneralNominalViewSupport249

def Outside (old : List (Entry Nat)) (reads : List Nat) : Prop :=
 ∀ name ∈ reads, ∀ entry ∈ old, entry.1 ≠ name

theorem parameter_closed (old : List (Entry Nat)) (safe : SafeOrder old) (p : Parameter) :
 Outside old (parameterReads (GeneralNominalRebaseViewSubst243.parameter (mapping old) p)) := by
 cases p with
 | type lo hi =>
   intro name member entry present
   rcases List.mem_append.mp member with member | member
   · exact GeneralPresenceOrderedExpansion249.type_rewrite_closed old safe lo name member entry present
   · exact GeneralPresenceOrderedExpansion249.type_rewrite_closed old safe hi name member entry present
 | row lo hi => intro name member; cases member

theorem descriptor_closed (old : List (Entry Nat)) (safe : SafeOrder old) (d : Descriptor) :
 Outside old (descriptorReads (GeneralNominalRebaseViewSubst243.descriptor (mapping old) d)) := by
 intro name member entry present
 obtain ⟨p,member,read⟩ := List.mem_flatMap.mp member
 obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
 exact parameter_closed old safe original name read entry present

theorem view_closed (old : List (Entry Nat)) (safe : SafeOrder old) (view : View) :
 Outside old (support (GeneralNominalRebaseViewSubst243.subst view (mapping old))) := by
 intro name member entry present
 rcases List.mem_append.mp member with ordinary | slots
 · exact GeneralPresenceOrderedExpansion249.rewrite_closed old safe view.ordinary name ordinary entry present
 · obtain ⟨reads,listed,read⟩ := List.mem_flatten.mp slots
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp listed
   rcases List.mem_append.mp read with left | nominal
   · rcases List.mem_append.mp left with slot | head
     · exact GeneralPresenceOrderedExpansion249.type_rewrite_closed old safe (view.slot index).ty name slot entry present
     · obtain ⟨term,found,used⟩ := List.mem_flatMap.mp head
       have found' : (view.heads index).map (fun term => term.subst (mapping old)) = some term := by
         simpa only [Option.mem_toList,GeneralNominalRebaseViewSubst243.subst] using found
       obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found'
       exact GeneralPresenceOrderedExpansion249.type_rewrite_closed old safe original name used entry present
   · obtain ⟨d,found,used⟩ := List.mem_flatMap.mp nominal
     have found' : (view.nominals index).map (GeneralNominalRebaseViewSubst243.descriptor (mapping old)) = some d := by
       simpa only [Option.mem_toList,GeneralNominalRebaseViewSubst243.subst] using found
     obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found'
     exact descriptor_closed old safe original name used entry present

theorem within_protected (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (view : View) :
 ∀ name ∈ support (GeneralNominalRebaseViewSubst243.subst view (mapping old)),
   ∀ entry ∈ fresh, entry.1 ≠ name := by
 intro name member entry present
 obtain ⟨original,found,equal⟩ := within entry present
 rw [← equal]
 exact view_closed old safe view name member original found

theorem typed_subst_cross (term : TyTerm α) (replacement : α → CompTerm Nat) :
 typedReads (term.subst replacement) = (typedReads term).flatMap (fun key => typedReads (replacement key).ty) := by
 induction term <;> simp_all [typedReads,TyTerm.subst,List.flatMap_append]

theorem mapped_type_closed (old : List (Entry Nat)) (replacement : α → CompTerm Nat)
 (closed : ∀ key, Outside old (typedReads (replacement key).ty)) (term : TyTerm α) :
 Outside old (typedReads (term.subst replacement)) := by
 rw [typed_subst_cross]
 intro name member entry present
 obtain ⟨key,_,read⟩ := List.mem_flatMap.mp member
 exact closed key name read entry present

theorem mapped_atom_closed (old : List (Entry Nat)) (replacement : α → CompTerm Nat)
 (closed : ∀ key, Outside old (typedReads (replacement key).ty)) (atom : PresenceNormalForm.Atom α) :
 Outside old (GeneralPresenceConsumerSupport246.atomTypedReads (GeneralNominalRebaseRawView243.atom replacement atom)) := by
 cases atom with
 | tyLe a b =>
   intro name member entry present
   rcases List.mem_append.mp member with member | member
   · exact mapped_type_closed old replacement closed a name member entry present
   · exact mapped_type_closed old replacement closed b name member entry present
 | rowLe a b => intro name member; cases member

theorem compiled_parameter_closed (old : List (Entry Nat)) (safe : SafeOrder old)
 (state : GeneralSourceState.State) (p : GeneralNominalState.Parameter state.slots) :
 Outside old (parameterReads (GeneralNominalRebaseRawView243.parameter state (mapping old) p)) := by
 cases p with
 | type bounds =>
   intro name member entry present
   rcases List.mem_append.mp member with member | member
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ name member entry present
   · exact GeneralPresenceOrderedSyntax247.mapping_closed old safe _ name member entry present
 | row bounds => intro name member; cases member

theorem compiled_descriptor_closed (old : List (Entry Nat)) (safe : SafeOrder old)
 (state : GeneralSourceState.State) (d : GeneralNominalState.Descriptor state.slots) :
 Outside old (descriptorReads (GeneralNominalRebaseRawView243.descriptor state (mapping old) d)) := by
 intro name member entry present
 obtain ⟨p,member,read⟩ := List.mem_flatMap.mp member
 obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
 exact compiled_parameter_closed old safe state original name read entry present

theorem compile_closed (old : List (Entry Nat)) (safe : SafeOrder old)
 (state : GeneralNominalState.State) :
 Outside old (support (GeneralNominalRebaseRawView243.compile state (mapping old))) := by
 have mapped : ∀ key, Outside old (typedReads (mapping old key).ty) :=
   GeneralPresenceOrderedSyntax247.mapping_closed old safe
 have slots : ∀ index, Outside old (typedReads (GeneralNominalRebaseRawView243.slot state.base (mapping old) index).ty) :=
   fun index => mapped (state.base.source index)
 intro name member entry present
 rcases List.mem_append.mp member with ordinary | slotReads
 · obtain ⟨atom,member,read⟩ := List.mem_flatMap.mp ordinary
   rcases List.mem_append.mp member with base | raw
   · obtain ⟨original,_,rfl⟩ := List.mem_map.mp base
     exact mapped_atom_closed old _ slots original name read entry present
   · obtain ⟨original,_,rfl⟩ := List.mem_map.mp raw
     exact mapped_atom_closed old _ mapped original name read entry present
 · obtain ⟨reads,listed,read⟩ := List.mem_flatten.mp slotReads
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp listed
   rcases List.mem_append.mp read with left | nominal
   · rcases List.mem_append.mp left with source | head
     · exact slots index name source entry present
     · obtain ⟨term,found,used⟩ := List.mem_flatMap.mp head
       have found' : (state.base.heads index).equation.map
           (fun term => term.subst (GeneralNominalRebaseRawView243.slot state.base (mapping old))) = some term := by
         simpa only [Option.mem_toList,GeneralNominalRebaseRawView243.compile] using found
       obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found'
       exact mapped_type_closed old _ slots original name used entry present
   · obtain ⟨d,found,used⟩ := List.mem_flatMap.mp nominal
     have found' : (state.nominals index).map
         (GeneralNominalRebaseRawView243.descriptor state.base (mapping old)) = some d := by
       simpa only [Option.mem_toList,GeneralNominalRebaseRawView243.compile] using found
     obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found'
     exact compiled_descriptor_closed old safe state.base original name used entry present

theorem compiled_within_protected (old fresh : List (Entry Nat)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (state : GeneralNominalState.State) :
 GeneralNominalOrderedRawExpansion249.Protected state old fresh := by
 intro name member entry present
 obtain ⟨original,found,equal⟩ := within entry present
 rw [← equal]
 exact compile_closed old safe state name member original found
end Yulang.GeneralNominalOrderedViewClosed249
