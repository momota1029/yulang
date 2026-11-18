import Yulang.GeneralNominalViewTypeTerms255
import Yulang.GeneralNominalAssignmentCongruence238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalViewTypeMap255
open Core.PresenceGeneration
open GeneralNominalRebaseRawView243
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalAssignmentCongruence238 (subtype_iff)
namespace T
abbrev parameter := GeneralNominalViewTypeTerms255.parameter
abbrev descriptor := GeneralNominalViewTypeTerms255.descriptor
abbrev ordinary := GeneralNominalViewTypeTerms255.ordinary
abbrev slot := GeneralNominalViewTypeTerms255.slot
abbrev terms := GeneralNominalViewTypeTerms255.terms
end T

def parameter (f : TyTerm Nat → TyTerm Nat) : Parameter → Parameter
 | .type lower upper => .type (f lower) (f upper)
 | .row lower upper => .row lower upper

def descriptor (f : TyTerm Nat → TyTerm Nat) (entry : Descriptor) : Descriptor :=
 ⟨entry.name,entry.arguments.map (parameter f)⟩
def ordinary (f : TyTerm Nat → TyTerm Nat) : PresenceNormalForm.Atom Nat → PresenceNormalForm.Atom Nat
 | .tyLe first last => .tyLe (f first) (f last)
 | .rowLe first last => .rowLe first last

def map (f : TyTerm Nat → TyTerm Nat) (view : View) : View where
 slots := view.slots
 slot := fun index => ⟨f (view.slot index).ty,(view.slot index).row⟩
 ordinary := view.ordinary.map (ordinary f)
 heads := fun index => (view.heads index).map f
 intervals := view.intervals
 nominals := fun index => (view.nominals index).map (descriptor f)

def ExactOn (f : TyTerm Nat → TyTerm Nat) (assignment : Assignment) (terms : List (TyTerm Nat)) : Prop :=
 ∀ term ∈ terms, Equivalent ((f term).eval model assignment) (term.eval model assignment)

theorem equivalent_iff (first : Equivalent a a') (last : Equivalent b b') :
 Equivalent a b ↔ Equivalent a' b' :=
 and_congr (subtype_iff first last) (subtype_iff last first)

theorem parameter_exact (f : TyTerm Nat → TyTerm Nat) (assignment : Assignment) (entry : Parameter)
 (same : ExactOn f assignment (T.parameter entry)) (value : Argument) :
 (parameter f entry).Fits assignment value ↔ entry.Fits assignment value := by
 cases entry with
 | type lower upper =>
   have lo := same lower (List.mem_cons_self ..)
   have hi := same upper (List.mem_cons_of_mem _ (List.mem_cons_self ..))
   cases value with
   | inl value =>
     exact and_congr (subtype_iff lo ⟨subtype_refl _,subtype_refl _⟩)
       (subtype_iff ⟨subtype_refl _,subtype_refl _⟩ hi)
   | inr => rfl
 | row => rfl

theorem fitsAll_exact (f : TyTerm Nat → TyTerm Nat) (assignment : Assignment) (parameters : List Parameter)
 (same : ExactOn f assignment (parameters.flatMap T.parameter)) (values : List Argument) :
 FitsAll assignment (parameters.map (parameter f)) values ↔ FitsAll assignment parameters values := by
 induction parameters generalizing values with
 | nil => cases values <;> constructor <;> intro h <;> cases h <;> exact .nil
 | cons first rest ih =>
   have firstEq := parameter_exact f assignment first (fun term member => same term (List.mem_append_left _ member))
   have restEq := ih (fun term member => same term (List.mem_append_right _ member))
   constructor
   · intro fits
     cases fits with
     | cons one remaining => exact .cons ((firstEq _).mp one) ((restEq _).mp remaining)
   · intro fits
     cases fits with
     | cons one remaining => exact .cons ((firstEq _).mpr one) ((restEq _).mpr remaining)

theorem descriptor_exact (f : TyTerm Nat → TyTerm Nat) (assignment : Assignment)
 (entry : Descriptor) (target : TyTerm Nat)
 (targetEq : Equivalent ((f target).eval model assignment) (target.eval model assignment))
 (same : ExactOn f assignment (T.descriptor entry)) :
 (descriptor f entry).Denotes assignment (f target) ↔ entry.Denotes assignment target := by
 unfold Descriptor.Denotes descriptor
 simp only [fitsAll_exact f assignment entry.arguments same]
 apply exists_congr
 intro values
 exact and_congr Iff.rfl (equivalent_iff targetEq ⟨subtype_refl _,subtype_refl _⟩)

theorem ordinary_exact (f : TyTerm Nat → TyTerm Nat) (assignment : Assignment)
 (atom : PresenceNormalForm.Atom Nat) (same : ExactOn f assignment (T.ordinary atom)) :
 (ordinary f atom).Holds model assignment ↔ atom.Holds model assignment := by
 cases atom with
 | tyLe first last =>
   exact subtype_iff (same first (List.mem_cons_self ..))
     (same last (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
 | rowLe => rfl

theorem models_exact (f : TyTerm Nat → TyTerm Nat) (view : View) (assignment : Assignment)
 (same : ExactOn f assignment (T.terms view)) :
 (map f view).Models assignment ↔ view.Models assignment := by
 have slots (index : Fin view.slots) : ExactOn f assignment (T.slot view index) :=
   fun term member => same term (GeneralNominalViewTypeTerms255.slot_mem view index member)
 have target (index : Fin view.slots) :
   Equivalent ((f (view.slot index).ty).eval model assignment) ((view.slot index).ty.eval model assignment) :=
   slots index _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)))
 have atoms : PresenceNormalForm.All model assignment ((map f view).ordinary) ↔
   PresenceNormalForm.All model assignment view.ordinary := by
   simp only [map,PresenceNormalForm.All,List.forall_mem_map]
   apply forall_congr'; intro atom
   apply forall_congr'; intro member
   exact ordinary_exact f assignment atom (fun term present => same term
     (GeneralNominalViewTypeTerms255.ordinary_mem view atom member present))
 unfold View.Models
 apply and_congr atoms
 apply and_congr
 · constructor
   · intro valid index term found
     have proof := valid index (f term) (by simp only [map,found,Option.map_some])
     exact (equivalent_iff (target index) (slots index term
       (List.mem_append_left _ (List.mem_append_right _ (by simp [found]))))).mp proof
   · intro valid index term found
     obtain ⟨original,present,rfl⟩ := Option.map_eq_some_iff.mp found
     exact (equivalent_iff (target index) (slots index original
       (List.mem_append_left _ (List.mem_append_right _ (by simp [present]))))).mpr (valid index original present)
 apply and_congr
 · apply forall_congr'; intro pair
   apply forall_congr'; intro member
   exact subtype_iff (target pair.1) (target pair.2)
 · constructor
   · intro valid index entry found
     have proof := valid index (descriptor f entry) (by simp only [map,found,Option.map_some])
     apply (descriptor_exact f assignment entry _ (target index) ?_).mp proof
     intro term member
     exact slots index term (List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry,by simp [found],member⟩))
   · intro valid index entry found
     obtain ⟨original,present,rfl⟩ := Option.map_eq_some_iff.mp found
     apply (descriptor_exact f assignment original _ (target index) ?_).mpr (valid index original present)
     intro term member
     exact slots index term (List.mem_append_right _ (List.mem_flatMap.mpr ⟨original,by simp [present],member⟩))
end Yulang.GeneralNominalViewTypeMap255
