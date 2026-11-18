import Yulang.GeneralRebasePlanTransport262
import Yulang.GeneralRebaseMergeFrame261

namespace Yulang.GeneralRebasePlanTransportExamples262
open GeneralRebasePlanTransport262
open GeneralRebaseMergeRequests261 (candidate packet)
open GeneralNominalCommonBridge (Assignment)

/-- Distinct ordinary-journal snapshots share this zero-input declaration's
actual binder table. No Good, raw-model, or satisfiability assumption is used. -/
theorem changing_atoms (first last : List (PresenceNormalForm.Atom Nat)) :
 Same (candidate first) (candidate last) := by
 refine ⟨rfl,rfl,rfl,?_,rfl⟩
 intro name
 have capture : GeneralNominalPacketSupport.capture (packet first) =
     GeneralNominalPacketSupport.capture (packet last) := by
   unfold GeneralNominalPacketSupport.capture
   rw [GeneralRebaseMergeFrame261.bindings_empty first,GeneralRebaseMergeFrame261.bindings_empty last]
   exact GeneralNominalPacketCodes.capture_seed _ _ rfl _ _ _ _
 unfold GeneralNominalCenters.Plan.binder
 dsimp only [candidate]
 rw [capture]
 rfl

theorem table_unchanged (first last : List (PresenceNormalForm.Atom Nat)) (owner : Nat)
 (outputs : List GeneralSourceState.Output) :
 GeneralRebaseStableClass261.facts (candidate first) owner outputs =
 GeneralRebaseStableClass261.facts (candidate last) owner outputs :=
 facts_eq _ _ (changing_atoms first last) owner outputs

theorem meaning_unchanged (first last : List (PresenceNormalForm.Atom Nat)) (owner : Nat)
 (assignment : Assignment) (fact : GeneralRebaseStep258.Fact) :
 GeneralRebaseStableClass261.Holds (candidate first) owner assignment fact ↔
 GeneralRebaseStableClass261.Holds (candidate last) owner assignment fact :=
 stable_class_holds _ _ (changing_atoms first last) owner assignment fact

/-- This does not assert that arbitrary atoms arise in a source trace or that
one packet's current raw model or Evidence certificate transports. -/
theorem class_effects_unchanged (first last : List (PresenceNormalForm.Atom Nat))
 (source : GeneralNominalCenteredSteps.State GeneralNominalCenteredHeadAllocMergeSource.roles)
 (root : GeneralSourceDictionaries.Occurrence GeneralNominalCenteredHeadAllocMergeSource.roles)
 (assignment : Assignment) :
 GeneralNominalVersionedEffects231.ClassEffects source root (candidate first) assignment ↔
 GeneralNominalVersionedEffects231.ClassEffects source root (candidate last) assignment :=
 class_effects _ _ (changing_atoms first last) source root assignment
end Yulang.GeneralRebasePlanTransportExamples262
