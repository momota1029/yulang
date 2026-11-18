import Yulang.GeneralNominalViewTypeMap255
namespace Yulang.GeneralNominalViewTypeImage255
open Core.PresenceGeneration
open GeneralNominalRebaseRawView243
open GeneralNominalViewTypeMap255

theorem parameter_terms (f : TyTerm Nat → TyTerm Nat) (entry : Parameter) :
 T.parameter (parameter f entry) = (T.parameter entry).map f := by
 cases entry <;> rfl

theorem descriptor_terms (f : TyTerm Nat → TyTerm Nat) (entry : Descriptor) :
 T.descriptor (descriptor f entry) = (T.descriptor entry).map f := by
 simp only [T.descriptor,GeneralNominalViewTypeTerms255.descriptor,GeneralNominalViewTypeMap255.descriptor,List.flatMap_map,List.map_flatMap]
 simp only [parameter_terms]

theorem ordinary_terms (f : TyTerm Nat → TyTerm Nat) (entry : PresenceNormalForm.Atom Nat) :
 T.ordinary (ordinary f entry) = (T.ordinary entry).map f := by
 cases entry <;> rfl

theorem slot_terms (f : TyTerm Nat → TyTerm Nat) (view : View) (index : Fin view.slots) :
 T.slot (map f view) index = (T.slot view index).map f := by
 simp only [T.slot,GeneralNominalViewTypeTerms255.slot,map,List.map_append,List.map_cons,List.map_nil]
 cases h : view.heads index <;> cases n : view.nominals index <;>
 simp [Option.toList,descriptor_terms]

theorem view_terms (f : TyTerm Nat → TyTerm Nat) (view : View) :
 T.terms (map f view) = (T.terms view).map f := by
 unfold T.terms GeneralNominalViewTypeTerms255.terms
 rw [List.map_append,List.map_flatMap,List.map_flatten,List.map_ofFn]
 congr 1
 · simp only [map,List.flatMap_map,ordinary_terms]
 · apply congrArg List.flatten
   apply congrArg List.ofFn
   funext index
   exact slot_terms f view index

theorem term_origin (f : TyTerm Nat → TyTerm Nat) (view : View) (term : TyTerm Nat)
 (member : term ∈ T.terms (map f view)) : ∃ original ∈ T.terms view, term = f original := by
 rw [view_terms] at member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact ⟨original,present,rfl⟩

theorem parameter_congr (f g : TyTerm Nat → TyTerm Nat) (entry : Parameter)
 (same : ∀ term ∈ T.parameter entry, f term = g term) : parameter f entry = parameter g entry := by
 cases entry with
 | row => rfl
 | type first last =>
   simp only [GeneralNominalViewTypeMap255.parameter,same first (List.mem_cons_self ..),same last (List.mem_cons_of_mem _ (List.mem_cons_self ..))]

theorem descriptor_congr (f g : TyTerm Nat → TyTerm Nat) (entry : Descriptor)
 (same : ∀ term ∈ T.descriptor entry, f term = g term) : descriptor f entry = descriptor g entry := by
 unfold GeneralNominalViewTypeMap255.descriptor
 congr 1
 apply List.map_congr_left
 intro argument present
 exact parameter_congr f g argument (fun term occurs => same term (List.mem_flatMap.mpr ⟨argument,present,occurs⟩))

theorem ordinary_congr (f g : TyTerm Nat → TyTerm Nat) (entry : PresenceNormalForm.Atom Nat)
 (same : ∀ term ∈ T.ordinary entry, f term = g term) : ordinary f entry = ordinary g entry := by
 cases entry with
 | rowLe => rfl
 | tyLe first last =>
   simp only [ordinary,same first (List.mem_cons_self ..),same last (List.mem_cons_of_mem _ (List.mem_cons_self ..))]

theorem map_congr (f g : TyTerm Nat → TyTerm Nat) (view : View)
 (same : ∀ term ∈ T.terms view, f term = g term) : map f view = map g view := by
 have slotSame (index : Fin view.slots) := fun term member => same term (GeneralNominalViewTypeTerms255.slot_mem view index member)
 have ordinarySame : view.ordinary.map (ordinary f) = view.ordinary.map (ordinary g) := by
   apply List.map_congr_left
   intro entry present
   exact ordinary_congr f g entry (fun term member => same term (GeneralNominalViewTypeTerms255.ordinary_mem view entry present member))
 have slots : (fun index => (⟨f (view.slot index).ty,(view.slot index).row⟩ : CompTerm Nat)) =
   (fun index => (⟨g (view.slot index).ty,(view.slot index).row⟩ : CompTerm Nat)) := by
   funext index
   rw [slotSame index _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))]
 have heads : (fun index => (view.heads index).map f) = (fun index => (view.heads index).map g) := by
   funext index
   cases h : view.heads index with
   | none => rfl
   | some term =>
     simp only [Option.map_some]
     congr 1
     exact slotSame index term (List.mem_append_left _ (List.mem_append_right _ (by simp [h])))
 have nominals : (fun index => (view.nominals index).map (descriptor f)) = (fun index => (view.nominals index).map (descriptor g)) := by
   funext index
   cases h : view.nominals index with
   | none => rfl
   | some entry =>
     simp only [Option.map_some]
     congr 1
     exact descriptor_congr f g entry (fun term member => slotSame index term
       (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,by simp [h],member⟩)))
 unfold map
 rw [ordinarySame,slots,heads,nominals]
theorem parameter_comp (f g : TyTerm Nat → TyTerm Nat) (entry : Parameter) :
 parameter f (parameter g entry) = parameter (f ∘ g) entry := by cases entry <;> rfl

theorem descriptor_comp (f g : TyTerm Nat → TyTerm Nat) (entry : Descriptor) :
 descriptor f (descriptor g entry) = descriptor (f ∘ g) entry := by
 simp only [GeneralNominalViewTypeMap255.descriptor,List.map_map]
 congr 1
 apply List.map_congr_left
 intro argument _
 exact parameter_comp f g argument

theorem ordinary_comp (f g : TyTerm Nat → TyTerm Nat) (entry : PresenceNormalForm.Atom Nat) :
 ordinary f (ordinary g entry) = ordinary (f ∘ g) entry := by cases entry <;> rfl

theorem map_comp (f g : TyTerm Nat → TyTerm Nat) (view : View) :
 map f (map g view) = map (f ∘ g) view := by
 simp only [map,List.map_map,Option.map_map]
 congr 1
 · apply List.map_congr_left
   intro entry _
   exact ordinary_comp f g entry
 · funext index
   cases view.nominals index with
   | none => rfl
   | some entry => exact congrArg some (descriptor_comp f g entry)

theorem parameter_id (entry : Parameter) : parameter id entry = entry := by cases entry <;> rfl

theorem descriptor_id (entry : Descriptor) : descriptor id entry = entry := by
 have h : GeneralNominalViewTypeMap255.parameter id = id := funext parameter_id
 cases entry
 simp [GeneralNominalViewTypeMap255.descriptor,h]

theorem ordinary_id (entry : PresenceNormalForm.Atom Nat) : ordinary id entry = entry := by cases entry <;> rfl

theorem map_id (view : View) : map id view = view := by
 have ho : ordinary id = id := funext ordinary_id
 have hd : GeneralNominalViewTypeMap255.descriptor id = id := funext descriptor_id
 cases view
 simp [map,ho,hd]
end Yulang.GeneralNominalViewTypeImage255
