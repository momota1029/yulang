import Yulang.GeneralDictionaryVersionedStep232
import Yulang.GeneralNominalVersionedCommitted232
import Yulang.GeneralNominalVersionedFrameFunctional232
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Normal form for the install-only migration fragment on the concrete 230
terminal example. This is NOT full-solver Stable, global termination, or a
completed successor SourceBoundary. Other administrative rules are not here. -/
namespace Yulang.GeneralDictionaryVersionedInstallClosed232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Snapshot
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalVersionedInstallStep232
open GeneralNominalCenters

 theorem raw_sites : installed.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := by
  change (installCore before.core effect.plan).erased.current.sites = _
  rw [GeneralNominalVersionedTerminal232.raw_eq terminal]
  rfl

theorem centers : installed.core.sites = [rootSite snapshot.seed root] := by
  change (installCore before.core effect.plan).sites = _
  rw [GeneralNominalVersionedTerminal232.sites_eq terminal]
  rfl

theorem edges_empty : installed.core.erased.current.edges = [] := by
  change after.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges effect.plan = []
  unfold GeneralNominalVersionedChildren232.edges
  rw [terminal]
  change [] ++ GeneralDictionaryOptionalInstall229.packet.children.map (fun child => (root,child)) ++ [] = []
  rw [GeneralDictionaryOptionalInstall229.children_empty]
  rfl

theorem generated_only (given : GeneralNominalSaturationState.Generated installed.core.erased.current root focus) :
    focus = root := by
  induction given with
  | root => rfl
  | child _ edge _ => rw [edges_empty] at edge; cases edge
  | alias _ _ last _ _ =>
    rw [raw_sites] at last
    cases List.mem_singleton.mp last
    rfl

theorem frame_plan (frame : GeneralNominalVersionedEvidence231.Frame registry installed.core root key plan) :
    plan = GeneralDictionaryVersionedReconstruction231.replayed :=
  GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centers frame
    GeneralDictionaryVersionedEvidence232.frame

theorem no_install (next : State roles) : ¬ Step registry root installed next := by
  intro action
  cases action with
  | install candidate enabled generated novel =>
    have focus := generated_only generated
    have framed : GeneralNominalVersionedEvidence231.Frame registry installed.core root
        candidate.plan.packet.declaration.id candidate.plan := by
      have fr := candidate.frame
      rw [enabled.registry_eq,enabled.snapshot_eq,focus] at fr
      exact fr
    have same := frame_plan framed
    apply novel
    rw [same]
    exact GeneralNominalVersionedCommitted232.replay_committed before effect

end Yulang.GeneralDictionaryVersionedInstallClosed232
