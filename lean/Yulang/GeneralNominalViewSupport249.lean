import Yulang.GeneralNominalOrderedRaw248
import Yulang.GeneralPresenceConsumerSupport246

/-! Finite typed support for every field of actual RawView243.View.Models.
Rows are preserved globally. No abstract model-stability premise is assumed. -/
namespace Yulang.GeneralNominalViewSupport249
open Core.PresenceGeneration PresenceNormalForm
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246

def parameterReads : Parameter → List Nat
 | .type lo hi => typedReads lo ++ typedReads hi
 | .row _ _ => []
def descriptorReads (d : Descriptor) : List Nat := d.arguments.flatMap parameterReads

def perSlot (view : View) (index : Fin view.slots) : List Nat :=
 typedReads (view.slot index).ty ++
 ((view.heads index).toList.flatMap typedReads) ++
 ((view.nominals index).toList.flatMap descriptorReads)

def support (view : View) : List Nat :=
 listTypedReads view.ordinary ++ (List.ofFn (perSlot view)).flatten

theorem slot_member (view : View) (index : Fin view.slots) (name : Nat)
 (member : name ∈ perSlot view index) : name ∈ support view := by
 apply List.mem_append_right
 apply List.mem_flatten.mpr
 exact ⟨perSlot view index,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩

theorem type_member (view : View) (index : Fin view.slots) (name : Nat)
 (member : name ∈ typedReads (view.slot index).ty) : name ∈ support view :=
 slot_member view index name (List.mem_append_left _ (List.mem_append_left _ member))

theorem head_member (view : View) (index : Fin view.slots) (term : TyTerm Nat)
 (found : view.heads index = some term) (name : Nat) (member : name ∈ typedReads term) :
 name ∈ support view := by
 apply slot_member view index name
 apply List.mem_append_left
 apply List.mem_append_right
 exact List.mem_flatMap.mpr ⟨term,by simp [found],member⟩

theorem descriptor_member (view : View) (index : Fin view.slots) (d : Descriptor)
 (found : view.nominals index = some d) (name : Nat) (member : name ∈ descriptorReads d) :
 name ∈ support view := by
 apply slot_member view index name
 apply List.mem_append_right
 exact List.mem_flatMap.mpr ⟨d,by simp [found],member⟩

theorem parameter_iff (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2) (p : Parameter)
 (types : ∀ name ∈ parameterReads p, (first name).1 = (last name).1) (value : Argument) :
 p.Fits first value ↔ p.Fits last value := by
 cases p with
 | type lo hi =>
   have a := type_eval_equal model first last rows lo (fun n h => types n (List.mem_append_left _ h))
   have b := type_eval_equal model first last rows hi (fun n h => types n (List.mem_append_right _ h))
   cases value <;> simp only [Parameter.Fits,a,b]
 | row lo hi =>
   cases value <;> simp only [Parameter.Fits,GeneralPresenceModelCongruence245.row_eval_equal model first last rows]

theorem fitsAll_forward (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2)
 (parameters : List Parameter) (values : List Argument)
 (types : ∀ name ∈ parameters.flatMap parameterReads, (first name).1 = (last name).1)
 (valid : FitsAll first parameters values) : FitsAll last parameters values := by
 induction valid with
 | nil => exact .nil
 | cons fit rest ih =>
   refine .cons ((parameter_iff first last rows _ ?_ _).mp fit) (ih ?_)
   · intro name member
     exact types name (List.mem_append_left _ member)
   · intro name member
     exact types name (List.mem_append_right _ member)

theorem fitsAll_iff (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2) (parameters : List Parameter) (values : List Argument)
 (types : ∀ name ∈ parameters.flatMap parameterReads, (first name).1 = (last name).1) :
 FitsAll first parameters values ↔ FitsAll last parameters values :=
 ⟨fitsAll_forward first last rows parameters values types,
 fitsAll_forward last first (fun n => (rows n).symm) parameters values (fun n h => (types n h).symm)⟩

theorem descriptor_iff (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2) (d : Descriptor) (target : TyTerm Nat)
 (types : ∀ name ∈ descriptorReads d, (first name).1 = (last name).1)
 (targetTypes : ∀ name ∈ typedReads target, (first name).1 = (last name).1) :
 d.Denotes first target ↔ d.Denotes last target := by
 simp only [Descriptor.Denotes,fitsAll_iff first last rows d.arguments _ types,
   type_eval_equal model first last rows target targetTypes]

theorem models_iff (view : View) (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2)
 (types : ∀ name ∈ support view, (first name).1 = (last name).1) :
 view.Models first ↔ view.Models last := by
 have slotEval (index : Fin view.slots) :
     (view.slot index).ty.eval model first = (view.slot index).ty.eval model last :=
   type_eval_equal model first last rows _ (fun n h => types n (type_member view index n h))
 unfold View.Models
 apply and_congr (GeneralPresenceConsumerSupport246.all_iff model first last rows view.ordinary
   (fun n h => types n (List.mem_append_left _ h)))
 apply and_congr
 · apply forall_congr'; intro index
   apply forall_congr'; intro term
   apply forall_congr'; intro found
   rw [slotEval index,type_eval_equal model first last rows term
     (fun n h => types n (head_member view index term found n h))]
 apply and_congr
 · apply forall_congr'; intro pair
   apply forall_congr'; intro _
   rw [slotEval pair.1,slotEval pair.2]
 · apply forall_congr'; intro index
   apply forall_congr'; intro d
   apply forall_congr'; intro found
   exact descriptor_iff first last rows d _
     (fun n h => types n (descriptor_member view index d found n h))
     (fun n h => types n (type_member view index n h))
end Yulang.GeneralNominalViewSupport249
