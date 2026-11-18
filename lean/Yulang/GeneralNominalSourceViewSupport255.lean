import Yulang.GeneralNominalViewTypeTerms255
import Yulang.GeneralPresenceSourceSupport255
namespace Yulang.GeneralNominalSourceViewSupport255
open Core.PresenceGeneration
open GeneralNominalState (typeSources rowSources sources)
open GeneralNominalRebaseRawView243
abbrev consumerTerms := GeneralNominalViewTypeTerms255.terms

theorem slot_source (state : GeneralNominalState.State) (index : Fin state.base.slots) :
 state.base.source index ∈ sources state :=
 List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨index,rfl⟩)))

theorem slot_row (state : GeneralNominalState.State) (index : Fin state.base.slots) :
 state.base.rowSource index ∈ sources state :=
 List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨index,rfl⟩)))

theorem slot_type (state : GeneralNominalState.State) (index : Fin state.base.slots) :
 typeSources (slot state.base CompTerm.var index).ty ⊆ sources state := by
 intro name member
 exact List.mem_singleton.mp member ▸ slot_source state index

theorem slot_rows (state : GeneralNominalState.State) (index : Fin state.base.slots) :
 rowSources (slot state.base CompTerm.var index).row ⊆ sources state := by
 intro name member
 exact List.mem_singleton.mp member ▸ slot_row state index

theorem base_type (state : GeneralNominalState.State) (term : TyTerm (Fin state.base.slots)) :
 typeSources (term.subst (slot state.base CompTerm.var)) ⊆ sources state :=
 GeneralPresenceSourceSupport255.type_subst term _ (slot_type state) (slot_rows state)

theorem ordinary_type (state : GeneralNominalState.State) (entry : PresenceNormalForm.Atom Nat)
 (present : entry ∈ state.ordinary) (term : TyTerm Nat)
 (member : term ∈ GeneralNominalViewTypeTerms255.ordinary (atom CompTerm.var entry)) :
 typeSources term ⊆ sources state := by
 have held : GeneralNominalState.atomSources entry ⊆ sources state := by
   intro name occurs
   exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,present,occurs⟩)
 cases entry with
 | rowLe first last => cases member
 | tyLe first last =>
   rcases List.mem_cons.mp member with same | rest
   · subst term
     rw [GeneralPresenceSourceSupport255.type_identity]
     exact fun _ occurs => held (List.mem_append_left _ occurs)
   · have same := List.mem_singleton.mp rest
     subst term
     rw [GeneralPresenceSourceSupport255.type_identity]
     exact fun _ occurs => held (List.mem_append_right _ occurs)

theorem parameter_type (state : GeneralNominalState.State) (entry : GeneralNominalState.Parameter state.base.slots)
 (term : TyTerm Nat) (member : term ∈ GeneralNominalViewTypeTerms255.parameter (parameter state.base CompTerm.var entry)) :
 typeSources term ⊆ sources state := by
 cases entry with
 | row bounds => cases member
 | type bounds =>
   rcases List.mem_cons.mp member with same | rest
   · subst term; exact slot_type state bounds.1
   · have same := List.mem_singleton.mp rest
     exact same ▸ slot_type state bounds.2

theorem descriptor_type (state : GeneralNominalState.State) (entry : GeneralNominalState.Descriptor state.base.slots)
 (term : TyTerm Nat) (member : term ∈ GeneralNominalViewTypeTerms255.descriptor (descriptor state.base CompTerm.var entry)) :
 typeSources term ⊆ sources state := by
 obtain ⟨argument,present,occurs⟩ := List.mem_flatMap.mp member
 obtain ⟨original,_,rfl⟩ := List.mem_map.mp present
 exact parameter_type state original term occurs

theorem compiled_terms (state : GeneralNominalState.State) (term : TyTerm Nat)
 (member : term ∈ consumerTerms (compile state CompTerm.var)) : typeSources term ⊆ sources state := by
 rcases List.mem_append.mp member with ordinary | field
 · obtain ⟨entry,present,occurs⟩ := List.mem_flatMap.mp ordinary
   rcases List.mem_append.mp present with base | extra
   · obtain ⟨original,_,rfl⟩ := List.mem_map.mp base
     cases original with
     | rowLe first last => cases occurs
     | tyLe first last =>
       rcases List.mem_cons.mp occurs with same | rest
       · subst term; exact base_type state first
       · have same := List.mem_singleton.mp rest
         subst term; exact base_type state last
   · obtain ⟨original,sourcePresent,rfl⟩ := List.mem_map.mp extra
     exact ordinary_type state original sourcePresent term occurs
 · obtain ⟨fields,present,occurs⟩ := List.mem_flatten.mp field
   obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
   rcases List.mem_append.mp occurs with first | nominal
   · rcases List.mem_append.mp first with slot | head
     · have same := List.mem_singleton.mp slot
       subst term; exact slot_type state index
     · have found := Option.mem_toList.mp head
       obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found
       exact base_type state original
   · obtain ⟨entry,present,occurs⟩ := List.mem_flatMap.mp nominal
     have found := Option.mem_toList.mp present
     obtain ⟨original,_,rfl⟩ := Option.map_eq_some_iff.mp found
     exact descriptor_type state original term occurs

theorem compiled_pool (state : GeneralNominalState.State) (term : TyTerm Nat)
 (member : term ∈ GeneralNominalViewTypeTerms255.pool (compile state CompTerm.var)) :
 typeSources term ⊆ sources state := by
 obtain ⟨consumer,present,occurs⟩ := List.mem_flatMap.mp member
 intro name read
 apply compiled_terms state consumer present
 rcases List.mem_append.mp occurs with lower | upper
 · exact GeneralPresenceSourceSupport255.union_atom_sources consumer term lower read
 · exact GeneralPresenceSourceSupport255.inter_atom_sources consumer term upper read
end Yulang.GeneralNominalSourceViewSupport255
