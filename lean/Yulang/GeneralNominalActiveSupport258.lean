import Yulang.GeneralNominalViewSupport249
namespace Yulang.GeneralNominalActiveSupport258
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalRebaseRawView243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalViewSupport249 (parameterReads descriptorReads)
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246
open CommonNominalFullCarrier

def used (view : View) (index : Fin view.slots) : Bool :=
 (view.heads index).isSome || (view.nominals index).isSome ||
 view.intervals.any (fun pair => index == pair.1 || index == pair.2)

def targetReads (view : View) (index : Fin view.slots) : List Nat :=
 if used view index then typedReads (view.slot index).ty else []

def perSlot (view : View) (index : Fin view.slots) : List Nat :=
 targetReads view index ++ (view.heads index).toList.flatMap typedReads ++
 (view.nominals index).toList.flatMap descriptorReads

def support (view : View) : List Nat :=
 listTypedReads view.ordinary ++ (List.ofFn (perSlot view)).flatten

theorem slot_member (view : View) (index : Fin view.slots) (name : Nat)
 (member : name ∈ perSlot view index) : name ∈ support view := by
 apply List.mem_append_right
 apply List.mem_flatten.mpr
 exact ⟨perSlot view index,List.mem_ofFn.mpr ⟨index,rfl⟩,member⟩

theorem target_member (view : View) (index : Fin view.slots) (active : used view index = true)
 (name : Nat) (member : name ∈ typedReads (view.slot index).ty) : name ∈ support view := by
 apply slot_member view index name
 apply List.mem_append_left
 apply List.mem_append_left
 simpa only [targetReads,active,ite_true] using member

theorem head_member (view : View) (index : Fin view.slots) (term : TyTerm Nat)
 (found : view.heads index = some term) (name : Nat) (member : name ∈ typedReads term) : name ∈ support view := by
 apply slot_member view index name
 apply List.mem_append_left
 apply List.mem_append_right
 exact List.mem_flatMap.mpr ⟨term,by simp [found],member⟩

theorem descriptor_member (view : View) (index : Fin view.slots) (d : Descriptor)
 (found : view.nominals index = some d) (name : Nat) (member : name ∈ descriptorReads d) : name ∈ support view := by
 apply slot_member view index name
 apply List.mem_append_right
 exact List.mem_flatMap.mpr ⟨d,by simp [found],member⟩

theorem head_used (view : View) (index : Fin view.slots) (found : view.heads index = some term) : used view index = true := by
 simp [used,found]

theorem nominal_used (view : View) (index : Fin view.slots) (found : view.nominals index = some d) : used view index = true := by
 simp [used,found]

theorem interval_left (view : View) (pair : Fin view.slots × Fin view.slots) (member : pair ∈ view.intervals) : used view pair.1 = true := by
 have foundAny : view.intervals.any (fun other => pair.1 == other.1 || pair.1 == other.2) = true :=
   List.any_eq_true.mpr ⟨pair,member,by simp⟩
 simp only [used,foundAny,Bool.or_true]

theorem interval_right (view : View) (pair : Fin view.slots × Fin view.slots) (member : pair ∈ view.intervals) : used view pair.2 = true := by
 have foundAny : view.intervals.any (fun other => pair.2 == other.1 || pair.2 == other.2) = true :=
   List.any_eq_true.mpr ⟨pair,member,by simp⟩
 simp only [used,foundAny,Bool.or_true]

/-- Only target slots actually read by Models require type equality. All row
values remain fixed, including row reads nested inside type expressions. -/
theorem models_iff (view : View) (first last : Assignment)
 (rows : ∀ name, (first name).2 = (last name).2)
 (types : ∀ name ∈ support view, (first name).1 = (last name).1) :
 view.Models first ↔ view.Models last := by
 have slotEval (index : Fin view.slots) (active : used view index = true) :
     (view.slot index).ty.eval model first = (view.slot index).ty.eval model last :=
   type_eval_equal model first last rows _ (fun n h => types n (target_member view index active n h))
 unfold View.Models
 apply and_congr (GeneralPresenceConsumerSupport246.all_iff model first last rows view.ordinary
   (fun n h => types n (List.mem_append_left _ h)))
 apply and_congr
 · apply forall_congr'; intro index
   apply forall_congr'; intro term
   apply forall_congr'; intro found
   rw [slotEval index (head_used view index found),type_eval_equal model first last rows term
     (fun n h => types n (head_member view index term found n h))]
 apply and_congr
 · apply forall_congr'; intro pair
   apply forall_congr'; intro member
   rw [slotEval pair.1 (interval_left view pair member),slotEval pair.2 (interval_right view pair member)]
 · apply forall_congr'; intro index
   apply forall_congr'; intro d
   apply forall_congr'; intro found
   exact GeneralNominalViewSupport249.descriptor_iff first last rows d _
     (fun n h => types n (descriptor_member view index d found n h))
     (fun n h => types n (target_member view index (nominal_used view index found) n h))
end Yulang.GeneralNominalActiveSupport258
