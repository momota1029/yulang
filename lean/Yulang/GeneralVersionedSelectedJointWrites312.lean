import Yulang.GeneralVersionedJointWriteExact312
import Yulang.GeneralVersionedRootWrites312
import Yulang.GeneralVersionedSelectedJointHead312
import Yulang.GeneralVersionedAliasChoice312
import Yulang.GeneralNominalVersionedSupportedCurrentHead237

set_option backward.isDefEq.respectTransparency false
/-! Compose the actual selector, aggregate ledger, and prospective typed
writes on one full assignment. The remaining premises no longer assert
existence of a completed packet, child certificates or a joined model. -/
namespace Yulang.GeneralVersionedSelectedJointWrites312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedSupportedCompletion237 (pool)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralNominalVersionedTraceSiteSupport237 (Covered)
open GeneralFiniteTypedWrites312 (Coherent Protected)
open GeneralVersionedJointWrites312 (rows protect)
open GeneralNominalCommonBridge (Assignment)

def TableReady (s : State roles) (e : Effect roles) (names : List Nat) : Prop :=
  ∀ m, Models s m → HeadModels e.plan.packet m → SchemaHolds e.plan e.plan.headSchema m → e.Live s.core m →
    Coherent (rows e.plan m) ∧ Protected (rows e.plan m) (protect s e names) m

theorem joint {roles : Roles.RoleDecls} {s : State roles} {e : Effect roles}
    {root : Occurrence roles} {children : List (Occurrence roles)}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (supported : Support s names) (sites : Covered s names)
    (ledger : IdCovered (pool names s e.plan) s e.plan.packet)
    (head : ∃ m, Models s m ∧ HeadEquations e.plan m)
    (writes : TableReady s e names) :
    ∃ m, Residual s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  obtain ⟨first,valid,headOK,classes⟩ :=
    GeneralVersionedSelectedJointHead312.effects_for_frame checked path pick frame head
  have raw := (GeneralVersionedSelectedJointHead312.report_for_frame frame valid headOK).2
  have covered := GeneralNominalVersionedMixedSeedLedger237.covered
    (GeneralNominalVersionedMixedSeedLedger237.reachable path) frame.context_eq ledger
  obtain ⟨models,headModel,schema,_,live⟩ := GeneralNominalVersionedSupportedCurrentHead237.selective_head
    names e.plan supported sites frame covered valid raw.1 raw.2.1 raw.2.2 headOK.2.2 classes
  obtain ⟨coherent,fixed⟩ := writes _ models headModel schema live
  exact ⟨_,GeneralVersionedJointWrites312.complete frame.context_eq supported models headModel schema live coherent fixed⟩

def InternalReady (s : State roles) (e : Effect roles) (names : List Nat) : Prop :=
  ∀ m, Models s m → HeadModels e.plan.packet m → SchemaHolds e.plan e.plan.headSchema m → e.Live s.core m →
    GeneralVersionedRootWrites312.FreeCoherent (GeneralVersionedRootWrites312.internalRows e.plan m) (protect s e names) ∧
    Protected (GeneralVersionedRootWrites312.internalRows e.plan m) (protect s e names) m

theorem joint_from_internal {roles : Roles.RoleDecls} {s : State roles} {e : Effect roles}
    {root : Occurrence roles} {children : List (Occurrence roles)}
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (supported : Support s names) (sites : Covered s names)
    (ledger : IdCovered (pool names s e.plan) s e.plan.packet)
    (head : ∃ m, Models s m ∧ HeadEquations e.plan m)
    (internal : InternalReady s e names) :
    ∃ m, Residual s e m := by
  apply joint checked path pick registryEq snapshot supported sites ledger head
  intro m valid head same live
  obtain ⟨coherent,fixed⟩ := internal m valid head same live
  exact GeneralVersionedRootWrites312.lift_table snapshot live coherent fixed

end Yulang.GeneralVersionedSelectedJointWrites312
