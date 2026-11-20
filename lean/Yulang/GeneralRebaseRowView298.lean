import Yulang.GeneralNominalOrderedRaw248
import Yulang.GeneralRebaseRowBasis298

namespace Yulang.GeneralRebaseRowView298
open Core.PresenceGeneration PresenceNormalForm
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseRawView243
open GeneralPresenceUsedSupport245 (rowReads)
open GeneralPresenceSubstitutionSupport244 (rowSources)
open GeneralRebaseRowBasis298

def parameterReads : Parameter → List Nat
 | .type lo hi => rowReads lo ++ rowReads hi
 | .row lo hi => rowSources lo ++ rowSources hi
def descriptorReads (d : Descriptor) : List Nat := d.arguments.flatMap parameterReads

def perSlot (view : View) (index : Fin view.slots) : List Nat :=
 rowReads (view.slot index).ty ++
 ((view.heads index).toList.flatMap rowReads) ++
 ((view.nominals index).toList.flatMap descriptorReads)

def support (view : View) : List Nat :=
 listRowReads view.ordinary ++ (List.ofFn (perSlot view)).flatten

theorem slot_member (view : View) (index : Fin view.slots) (name : Nat)
 (member : name ∈ perSlot view index) : name ∈ support view := by
 apply List.mem_append_right
 apply List.mem_flatten.mpr
 exact ⟨perSlot view index,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩

theorem type_member (view : View) (index : Fin view.slots) (name : Nat)
 (member : name ∈ rowReads (view.slot index).ty) : name ∈ support view :=
 slot_member view index name (List.mem_append_left _ (List.mem_append_left _ member))

theorem head_member (view : View) (index : Fin view.slots) (term : TyTerm Nat)
 (found : view.heads index = some term) (name : Nat) (member : name ∈ rowReads term) :
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
 (types : ∀ name, (first name).1 = (last name).1) (p : Parameter)
 (rows : ∀ name ∈ parameterReads p, (first name).2 = (last name).2) (value : Argument) :
 p.Fits first value ↔ p.Fits last value := by
 cases p with
 | type lo hi =>
   have a := type_eval_equal model first last types lo (fun n h => rows n (List.mem_append_left _ h))
   have b := type_eval_equal model first last types hi (fun n h => rows n (List.mem_append_right _ h))
   cases value <;> simp only [Parameter.Fits,a,b]
 | row lo hi =>
   have a := GeneralRebaseFiniteRowReads285.local_row_eval model first last lo (fun n h => rows n (List.mem_append_left _ h))
   have b := GeneralRebaseFiniteRowReads285.local_row_eval model first last hi (fun n h => rows n (List.mem_append_right _ h))
   cases value <;> simp only [Parameter.Fits,a,b]

theorem fitsAll_forward (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1)
 (parameters : List Parameter) (values : List Argument)
 (rows : ∀ name ∈ parameters.flatMap parameterReads, (first name).2 = (last name).2)
 (valid : FitsAll first parameters values) : FitsAll last parameters values := by
 induction valid with
 | nil => exact .nil
 | cons fit rest ih =>
   refine .cons ((parameter_iff first last types _ ?_ _).mp fit) (ih ?_)
   · intro name member
     exact rows name (List.mem_append_left _ member)
   · intro name member
     exact rows name (List.mem_append_right _ member)

theorem fitsAll_iff (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1) (parameters : List Parameter) (values : List Argument)
 (rows : ∀ name ∈ parameters.flatMap parameterReads, (first name).2 = (last name).2) :
 FitsAll first parameters values ↔ FitsAll last parameters values :=
 ⟨fitsAll_forward first last types parameters values rows,
 fitsAll_forward last first (fun n => (types n).symm) parameters values (fun n h => (rows n h).symm)⟩

theorem descriptor_iff (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1) (d : Descriptor) (target : TyTerm Nat)
 (rows : ∀ name ∈ descriptorReads d, (first name).2 = (last name).2)
 (targetTypes : ∀ name ∈ rowReads target, (first name).2 = (last name).2) :
 d.Denotes first target ↔ d.Denotes last target := by
 simp only [Descriptor.Denotes,fitsAll_iff first last types d.arguments _ rows,
   type_eval_equal model first last types target targetTypes]

theorem models_iff (view : View) (first last : Assignment)
 (types : ∀ name, (first name).1 = (last name).1)
 (rows : ∀ name ∈ support view, (first name).2 = (last name).2) :
 view.Models first ↔ view.Models last := by
 have slotEval (index : Fin view.slots) :
     (view.slot index).ty.eval model first = (view.slot index).ty.eval model last :=
   type_eval_equal model first last types _ (fun n h => rows n (type_member view index n h))
 unfold View.Models
 apply and_congr (GeneralRebaseRowBasis298.all_iff model first last types view.ordinary
   (fun n h => rows n (List.mem_append_left _ h)))
 apply and_congr
 · apply forall_congr'; intro index
   apply forall_congr'; intro term
   apply forall_congr'; intro found
   rw [slotEval index,type_eval_equal model first last types term
     (fun n h => rows n (head_member view index term found n h))]
 apply and_congr
 · apply forall_congr'; intro pair
   apply forall_congr'; intro _
   rw [slotEval pair.1,slotEval pair.2]
 · apply forall_congr'; intro index
   apply forall_congr'; intro d
   apply forall_congr'; intro found
   exact descriptor_iff first last types d _
     (fun n h => rows n (descriptor_member view index d found n h))
     (fun n h => rows n (type_member view index n h))
end Yulang.GeneralRebaseRowView298
