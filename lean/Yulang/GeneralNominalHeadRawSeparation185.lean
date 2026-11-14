import Yulang.GeneralNominalHeadPacketSupport185
import Yulang.GeneralNominalHeadSiteSupport185
import Yulang.GeneralNominalHeadLedgerFrame182

/-! Complete raw-journal support exclusion for the actual V6 head-step path.
Both centered and historical/live effect ledgers are retained as the precise
remaining preservation obligation; no old centered-step reachability is used. -/
namespace Yulang.GeneralNominalHeadRawSeparation185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepAncestry (InstalledDepthBound)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadWFBoundary (boundary)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem trace_raw_separate
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (high : 7 ≤ purpose) :
    fresh context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.rawSources state.core.erased.current := by
  intro present
  rcases List.mem_append.mp present with present | present
  · rcases List.mem_append.mp present with present | present
    · exact GeneralNominalHeadSiteSupport185.trace_sources_separate source bound path high present
    · obtain ⟨packet,member,present⟩ := List.mem_flatMap.mp present
      exact GeneralNominalHeadPacketSupport185.historical_packet_separate source bound path packet member high present
  · obtain ⟨site,member,present⟩ := List.mem_flatMap.mp present
    exact GeneralNominalHeadSiteSupport185.trace_sites_separate source bound path high site member present

theorem wf_raw_separate
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∉
      GeneralNominalRawFrame179.rawSources state.core.erased.current := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ :=
    GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  rw [(GeneralNominalCenteredHeadStepTrace.configuration_trace path).1]
  exact trace_raw_separate source
    (GeneralNominalCenteredHeadStepAncestry.installed_depth_bound point ground) path high

def Allocated (state : State roles) (names : Fin count → Nat) : Prop :=
  ∀ index, ∃ invocation declaration purpose owner position, 7 ≤ purpose ∧
    names index = fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position

noncomputable def residualSources (state : State roles) : List Nat :=
  GeneralNominalModeLedger181.ledgerSources state.core ++ GeneralNominalHeadLedgerFrame182.ledgerSources state

theorem wf_overlap_iff_residual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (high : 7 ≤ purpose) :
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      GeneralNominalHeadLedgerFrame182.fullSources state ↔
    fresh state.core.erased.current.context.state.seed invocation declaration purpose owner position ∈
      residualSources state := by
  simp only [GeneralNominalHeadLedgerFrame182.fullSources,GeneralNominalModeLedger181.fullSources,
    residualSources,List.mem_append, wf_raw_separate reachable high, false_or]

theorem wf_raw_assign
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (allocated : Allocated state names) (model : Assignment)
    (valid : GeneralNominalSaturationState.Models state.core.erased.current model) :
    GeneralNominalSaturationState.Models state.core.erased.current
      (GeneralNominalCenteredModelExtension.assign model names values) := by
  apply GeneralNominalRawFrame179.raw_models_frame state.core.erased.current _ valid
  apply GeneralNominalCenteredFrame179.assign_agree
  intro index
  obtain ⟨invocation,declaration,purpose,owner,position,high,equal⟩ := allocated index
  rw [equal]
  exact wf_raw_separate reachable high

theorem wf_models_assign
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (allocated : Allocated state names) (model : Assignment) (valid : Models state model)
    (kept : ∀ index, names index ∈ residualSources state → values index = (model (names index)).1) :
    Models state (GeneralNominalCenteredModelExtension.assign model names values) := by
  apply (GeneralNominalHeadLedgerFrame182.models_iff state ?_).mp valid
  intro name member
  symm
  apply GeneralNominalCenteredModelExtension.assign_preserves
  intro index equal
  have present : names index ∈ GeneralNominalHeadLedgerFrame182.fullSources state := equal ▸ member
  have residual : names index ∈ residualSources state := by
    obtain ⟨invocation,declaration,purpose,owner,position,high,named⟩ := allocated index
    rw [named] at present ⊢
    exact (wf_overlap_iff_residual reachable high).mp present
  simpa only [equal] using kept index residual

end Yulang.GeneralNominalHeadRawSeparation185
