import Yulang.GeneralDeclarativeVersionedPhysical342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
namespace Yulang.GeneralDeclarativeVersionedCurrent342
open GeneralWherePhysicalActive319 (active ctx refines)
open GeneralWherePhysicalPast319 (point pointCtx)
open GeneralWherePhysicalCurrentRead319 (plan packet locate)
open GeneralWherePhysicalCurrentFrame319 (prepared frame no_reserved)
open GeneralWherePhysicalCommit319 (final)
open GeneralWherePhysicalChildCert319 (final_sources)
open GeneralWhereOriginSingleSource318 (registry declaration)
open GeneralWhereOriginSingleCells318 (loNow)
open GeneralWhereOriginSingleModel318 (presentLo)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralDeclarativeVersionedPhysical342 (current observed transported holds_now actual_children)
open GeneralNominalCenters (Plan)
open GeneralNominalState (sources)
open GeneralWhereVersionCompiler317 (children)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalVersionedAllocation231 (Fresh keys)
open GeneralNominalIdentities (source Origin)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (roles root)

theorem root_reserved (key : Origin) (reserved : source active.seed key ∈ GeneralVersionedInstallDomain313.reserve packet) :
    source active.seed key ∉ sources active := by
  have small := GeneralVersionedInstallDomain313.reserve_purpose packet reserved
  intro hit
  rcases final_sources hit with before | fresh
  · exact no_reserved key reserved before
  · obtain ⟨o,h,e⟩ := presentLo.high (t := active) rfl
    exact GeneralVersionedHighOrigins315.distinct (a := key) (b := o) (by omega) active.seed (fresh.trans e)

theorem located : GeneralNominalRecursiveCandidates.arguments ctx (inputs root) = some current.packet.bounds :=
  GeneralDictionaryRefinedLocations.arguments pointCtx ctx refines (inputs root) _ locate

theorem current_prepared (m : Assignment) (fit : Models final m) :
    Prepared registry ctx root declaration := by
  refine ⟨GeneralDictionaryRefinedLocations.metadata pointCtx ctx refines rfl registry prepared.1,
    GeneralNominalRefinements.linked refines _ prepared.2.1,current.packet.bounds,located,?_,?_,m,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff current.packet m).mpr (holds_now m fit).head⟩
  · change Fresh active registry root.identity current.packet.bindings
    rw [GeneralNominalCenteredHeadMatPlanData.bindings transported]
    intro key present used
    exact False.elim (root_reserved key (List.mem_map.mpr ⟨key,present,rfl⟩) used)
  · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report current.packet)
    rw [GeneralRebaseRetarget275.report (after := ctx) plan refines rfl observed]
    apply (GeneralNominalSlotFacts198.finished_report refines.base.embed _).mpr
    change GeneralNominalRecursiveInspection.Finished (GeneralNominalRecursiveCandidates.report pointCtx declaration [(GeneralWherePhysicalCurrentRead319.zero,GeneralWherePhysicalCurrentRead319.zero)])
    rw [GeneralWherePhysicalCurrentRead319.exact_report]
    exact ⟨rfl,rfl,rfl⟩

/-- Unlike C319's install-time frame, this one is indexed by the
actual post-transaction centered state. It still certifies versioned
where Holds, never the old-format packet's full Holds. -/
theorem after_frame (m : Assignment) (fit : Models final m) :
    Frame registry final.mixed.core root declaration.id current := by
  refine ⟨rfl,rfl,rfl,rfl,List.mem_append_left _ frame.raw_recorded,
    List.mem_append_left _ frame.center_recorded,frame.visible,frame.role_eq,located,current_prepared m fit⟩

theorem current_parent (m : Assignment) (fit : Models final m) :
    Frame registry final.mixed.core root declaration.id current ∧ Holds current m ∧
      GeneralNominalVersionedEffects231.ClassEffects final.mixed.core root current m :=
  ⟨after_frame m fit,GeneralDeclarativeVersionedPhysical342.actual_model_packet m fit⟩

end Yulang.GeneralDeclarativeVersionedCurrent342
