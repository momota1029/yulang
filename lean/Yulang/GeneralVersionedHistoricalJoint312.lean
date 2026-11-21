import Yulang.GeneralVersionedSelectedJointWrites312
import Yulang.GeneralVersionedAliasHeadWrites312
import Yulang.GeneralVersionedSemanticPeer312

set_option backward.isDefEq.respectTransparency false
/-! Historical actual readback plus finite binder/child tables constructs a
full joint witness without assuming a completed current head or output model.
Both stages use one support/ledger certificate; no replay frame is required. -/
namespace Yulang.GeneralVersionedHistoricalJoint312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (Coherent Protected)
open GeneralNominalSaturationState (Alias)
open GeneralVersionedSelectedJointWrites312 (InternalReady)
variable {roles : Roles.RoleDecls} {s : State roles} {registry : Registry}
  {root : Occurrence roles} {children : List (Occurrence roles)} {e : Effect roles} {past : Plan roles}

def HeadTableReady (s : State roles) (now past : Plan roles) (names : List Nat) : Prop :=
  ∀ m, Models s m → HeadModels now.packet m →
    Coherent (GeneralVersionedAliasHeadWrites312.rows now past m) ∧
    Protected (GeneralVersionedAliasHeadWrites312.rows now past m) (GeneralVersionedAliasHeadWrites312.pool now names) m

theorem reduce_ledger {p : Plan roles} (supported : Support s names)
    (ledger : IdCovered (GeneralNominalVersionedSupportedCompletion237.pool names s p) s p.packet) :
    GeneralVersionedSemanticPeer312.Sufficient s p.packet := by
  refine ⟨names,supported,?_⟩
  intro entry member seen
  exact ledger entry member (List.mem_append_left _ seen)

theorem head_from_history {now : Plan roles}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame (Compiled registry) s.core now.packet.site.occurrence now.packet.declaration.id now)
    (history : past ∈ s.plans)
    (alias : Alias s.core.erased.current now.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (declaration : now.packet.declaration = past.packet.declaration)
    (inhabited : ∃ m, Models s m)
    (support : Support s names)
    (ledger : IdCovered (GeneralNominalVersionedSupportedCompletion237.pool names s now) s now.packet)
    (binders : HeadTableReady s now past names) :
    ∃ m, Models s m ∧ HeadEquations now m := by
  obtain ⟨first,valid⟩ := inhabited
  have initial := (GeneralVersionedAliasReport312.from_alias checked path past now history frame.center_recorded
    frame.context_eq frame.located alias declaration first valid).2
  obtain ⟨next,live,ready⟩ := GeneralVersionedSemanticPeer312.full_head_of_trace path frame.context_eq
    valid initial (reduce_ledger support ledger)
  obtain ⟨coherent,fixed⟩ := binders next live ready
  obtain ⟨models,_,head⟩ := GeneralVersionedAliasHeadWrites312.complete checked path frame history alias declaration
    support next live ready coherent fixed
  exact ⟨_,models,head⟩

theorem joint
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (history : past ∈ s.plans)
    (alias : Alias s.core.erased.current e.plan.packet.site.occurrence.identity past.packet.site.occurrence.identity)
    (declaration : e.plan.packet.declaration = past.packet.declaration)
    (inhabited : ∃ m, Models s m)
    (supported : Support s names) (sites : Covered s names)
    (ledger : IdCovered (GeneralNominalVersionedSupportedCompletion237.pool names s e.plan) s e.plan.packet)
    (binders : HeadTableReady s e.plan past names)
    (internal : InternalReady s e names) : ∃ m, Residual s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  exact GeneralVersionedSelectedJointWrites312.joint_from_internal checked path pick registryEq snapshot
    supported sites ledger (head_from_history checked path frame history alias declaration inhabited supported ledger binders)
    internal

end Yulang.GeneralVersionedHistoricalJoint312
