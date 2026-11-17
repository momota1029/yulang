import Yulang.GeneralNominalRebaseRawView243
import Yulang.GeneralNominalCenteredFrame179
set_option backward.isDefEq.respectTransparency false
/-! A finite semantic read set for the expression-valued raw View. -/
namespace Yulang.GeneralNominalRebaseViewSupport243
open GeneralNominalRebaseRawView243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCenteredModelExtension
open GeneralNominalState (typeSources rowSources atomSources)
open Core.PresenceGeneration (CompTerm)

def parameterSources : Parameter → List Nat
 | .type lower upper => typeSources lower ++ typeSources upper
 | .row lower upper => rowSources lower ++ rowSources upper

def descriptorSources (descriptor : Descriptor) : List Nat :=
 descriptor.arguments.flatMap parameterSources

def slotSources (view : View) (index : Fin view.slots) : List Nat :=
 (typeSources (view.slot index).1 ++ rowSources (view.slot index).2) ++
 ((view.heads index).toList.flatMap typeSources ++
   (view.nominals index).toList.flatMap descriptorSources)

def sources (view : View) : List Nat :=
 view.ordinary.flatMap atomSources ++ (List.ofFn (slotSources view)).flatten

theorem slot_mem (view : View) (index : Fin view.slots) : slotSources view index ⊆ sources view := by
 intro name member
 exact List.mem_append_right _ (List.mem_flatten.mpr ⟨slotSources view index,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩)

theorem parameter_iff (parameter : Parameter) {first last : Assignment}
 (same : Agree (parameterSources parameter) first last) (value) :
 parameter.Fits first value ↔ parameter.Fits last value := by
 cases parameter with
 | type lower upper =>
   cases value with
   | inl value =>
     simp only [Parameter.Fits,type_eval_same lower (fun name member => same name (List.mem_append_left _ member)),
       type_eval_same upper (fun name member => same name (List.mem_append_right _ member))]
   | inr value => rfl
 | row lower upper =>
   cases value with
   | inl value => rfl
   | inr value =>
     simp only [Parameter.Fits,row_eval_same lower (fun name member => same name (List.mem_append_left _ member)),
       row_eval_same upper (fun name member => same name (List.mem_append_right _ member))]

theorem fitsAll (parameters : List Parameter) {first last : Assignment}
 (same : Agree (parameters.flatMap parameterSources) first last)
 (valid : FitsAll first parameters values) : FitsAll last parameters values := by
 revert same
 induction valid with
 | nil => intro _; exact .nil
 | @cons parameters values parameter value fit rest ih =>
   intro same
   apply FitsAll.cons
   · exact (parameter_iff parameter (fun name member => same name
       (List.mem_append_left _ member)) value).mp fit
   · exact ih (fun name member => same name (List.mem_append_right _ member))

theorem descriptor_iff (descriptor : Descriptor) (target : Core.PresenceGeneration.TyTerm Nat)
 {first last : Assignment} (same : Agree (typeSources target ++ descriptorSources descriptor) first last) :
 descriptor.Denotes first target ↔ descriptor.Denotes last target := by
 have targetEq := type_eval_same target (fun name member => same name (List.mem_append_left _ member))
 have argumentEq : Agree (descriptorSources descriptor) first last :=
   fun name member => same name (List.mem_append_right _ member)
 constructor
 · rintro ⟨values,fit,equal⟩
   exact ⟨values,fitsAll descriptor.arguments argumentEq fit,by rw [← targetEq]; exact equal⟩
 · rintro ⟨values,fit,equal⟩
   exact ⟨values,fitsAll descriptor.arguments (fun name member => (argumentEq name member).symm) fit,
     by rw [targetEq]; exact equal⟩

theorem models_iff (view : View) {first last : Assignment} (same : Agree (sources view) first last) :
 view.Models first ↔ view.Models last := by
 have slotEq (index : Fin view.slots) :
   (view.slot index).1.eval CommonNominalFullCarrier.model first =
   (view.slot index).1.eval CommonNominalFullCarrier.model last :=
   type_eval_same _ (fun name member => same name (slot_mem view index
     (List.mem_append_left _ (List.mem_append_left _ member))))
 have atoms : PresenceNormalForm.All CommonNominalFullCarrier.model first view.ordinary ↔
   PresenceNormalForm.All CommonNominalFullCarrier.model last view.ordinary := by
   apply forall_congr'; intro atom
   apply forall_congr'; intro member
   exact atom_same atom (fun name present => same name (List.mem_append_left _
     (List.mem_flatMap.mpr ⟨atom,member,present⟩)))
 unfold View.Models
 apply and_congr atoms
 apply and_congr
 · apply forall_congr'; intro index
   apply forall_congr'; intro term
   apply forall_congr'; intro recorded
   have termEq := type_eval_same (first := first) (last := last) term (fun name member => same name
     (slot_mem view index (List.mem_append_right _ (List.mem_append_left _
       (List.mem_flatMap.mpr ⟨term,by simp [recorded],member⟩)))))
   rw [slotEq index,termEq]
 · apply and_congr
   · apply forall_congr'; intro pair
     apply forall_congr'; intro member
     rw [slotEq pair.1,slotEq pair.2]
   · apply forall_congr'; intro index
     apply forall_congr'; intro descriptor
     apply forall_congr'; intro recorded
     apply descriptor_iff
     intro name member
     apply same name
     apply slot_mem view index
     rcases List.mem_append.mp member with target | argument
     · exact List.mem_append_left _ (List.mem_append_left _ target)
     · exact List.mem_append_right _ (List.mem_append_right _
         (List.mem_flatMap.mpr ⟨descriptor,by simp [recorded],argument⟩))
end Yulang.GeneralNominalRebaseViewSupport243
