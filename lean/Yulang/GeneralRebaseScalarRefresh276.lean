import Yulang.GeneralRebaseNonleafTransport276
import Yulang.GeneralDictionaryInspectionHeads215

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseScalarRefresh276
open GeneralNominalState (State Known Models)
open GeneralNominalRefinements (Refines)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionHeads215
open GeneralNominalFiniteHeadInversion (head)
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier (subtype_refl)
open GeneralNominalSlotReport198 (report)
open GeneralNominalSlotObservation198 (bounds)

theorem nominal_none {state : State} (slot : Fin state.base.slots) (base : Inference.Base)
 (known : state.view.heads slot = .scalar base) : state.nominals slot = none := by
 cases h : state.nominals slot with
 | none => rfl
 | some descriptor =>
   have opaqueHead := state.bodies_opaque slot descriptor h
   rw [known] at opaqueHead
   cases opaqueHead

theorem scalar_head {before after : State} (ref : Refines before after)
 (m : Assignment) (valid : Models after m) (slot : Fin before.base.slots) (base : Inference.Base)
 (seen : before.view.heads slot = .scalar base) :
 after.view.heads (ref.base.embed slot) = .scalar base := by
 have old := GeneralNominalRefinements.models ref m valid
 have tag := scalar_slot old seen
 have oldKnown : Known before (before.base.source slot) := by
   refine ⟨slot,rfl,Or.inl ?_⟩
   simp [GeneralNormalizedObservation.Snapshot.graph,seen,GeneralNormalizedObservation.Head.node]
 obtain ⟨loc,equal,chosen⟩ := ref.known _ oldKnown
 have same : loc = ref.base.embed slot := after.base.source_injective (equal.trans (ref.base.source slot).symm)
 subst loc
 have expected : Tagged (m (after.base.source (ref.base.embed slot))).1 (.base base) := by
   rw [ref.base.source slot]
   exact tag
 rcases chosen with graph|⟨descriptor,recorded⟩
 · cases observed : after.view.heads (ref.base.embed slot) with
   | deferred reason =>
     exact False.elim (graph (by simp [GeneralNormalizedObservation.Snapshot.graph,observed,GeneralNormalizedObservation.Head.node]))
   | scalar actual =>
     have actualTag := scalar_slot valid observed
     have b := tag_subtype actualTag expected (subtype_refl _)
     cases b
     rfl
   | structural kind children =>
     have actual := structural_slot valid observed
     have impossible := tag_subtype actual expected (subtype_refl _)
     generalize after.view.shapes kind = shape at impossible
     cases shape <;> cases impossible
 · have actualTag := nominal_slot valid recorded
   have impossible := tag_subtype actualTag expected (subtype_refl _)
   cases impossible

theorem scalar_inspect {state : State} (slot : Fin state.base.slots) (base : Inference.Base)
 (seen : state.view.heads slot = .scalar base) (origin : Option Origin) :
 inspect state (.scalar base) (slot,slot) origin =
   Report.visit (slot,slot) origin (.scalar base) {} := by
 simp [inspect,nominal_none slot base seen,seen]

theorem scalar_report_mapped {before after : State} (ref : Refines before after)
 (m : Assignment) (valid : Models after m) (slot : Fin before.base.slots) (base : Inference.Base)
 (seen : before.view.heads slot = .scalar base) (origin : Option Origin) :
 inspect after (.scalar base) (bounds ref.base.embed (slot,slot)) origin =
 report ref.base.embed (inspect before (.scalar base) (slot,slot) origin) := by
 have retained := scalar_head ref m valid slot base seen
 change inspect after (.scalar base) (ref.base.embed slot,ref.base.embed slot) origin = _
 rw [scalar_inspect _ base retained,scalar_inspect _ base seen,GeneralNominalSlotReport198.report_visit]
 rfl

theorem no_scalar_in_nominal_contract {state : State} (slot : Fin state.base.slots) (base : Inference.Base) :
 ¬ GeneralNominalRefinementTrace197.Observed state (.scalar base) (slot,slot) := by
 intro seen
 cases seen

end Yulang.GeneralRebaseScalarRefresh276
