import Yulang.GeneralRebaseFullEdgeBasis279
import Yulang.GeneralRebaseReachableNovelty279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28400
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseFullEdgeProgress279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseClosedChildShape279 (ClosedArguments)
open GeneralRebaseFullEdgeBasis279 (OnTrace finite_full_edges exact_project)
open GeneralRebaseInstallNovelty279 (Edge FreshChild LostModel)
open GeneralRebaseProjectedEdgeCount279 (Seen Fresh)
open GeneralRebaseSourceEdgeBasis279 (project)
open GeneralRebaseWitnessTrace279 (Covers accessible_from)
open GeneralRebaseWitnessBudget279 (Fact consumed_model)
open GeneralRebaseWitnessRegressions279 (uncount)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseQuietBound277 (Counted)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {start before after : State roles}

theorem projected_iff (source : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r) (closed : ClosedArguments (registry r))
    (one : B4Target.Steps (Actual r root) start before)
    (two : B4Target.Steps (Actual r root) start after) :
    Fresh before after ↔ ∃ e : Edge roles, e ∉ before.core.erased.current.edges ∧ e ∈ after.core.erased.current.edges := by
  constructor
  · rintro ⟨key,old,new⟩
    obtain ⟨e,seen,rfl⟩ := List.mem_map.mp new
    exact ⟨e,fun prev => old (List.mem_map.mpr ⟨e,prev,rfl⟩),seen⟩
  · rintro ⟨fresh,old,new⟩
    refine ⟨project fresh,?_,List.mem_map.mpr ⟨fresh,new,rfl⟩⟩
    intro seen
    obtain ⟨e,prev,eq⟩ := List.mem_map.mp seen
    exact old ((exact_project source checked closed one two prev new eq) ▸ prev)

theorem graph_only_spends_projected (source : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r) (closed : ClosedArguments (registry r))
    (path : B4Target.Steps (Actual r root) start before) (effect : Effect roles)
    (actual : Actual r root before (install before effect))
    (enabled : GeneralNominalVersionedMixedKernel234.Installable (registry r) before effect)
    (novel : ¬ GeneralNominalVersionedMixedKernel234.Committed before effect.plan)
    (silent : GeneralRebaseInstallNovelty279.FullSilent before effect) :
    Fresh before (install before effect) := by
  have child := (GeneralRebaseInstallNovelty279.graph_only enabled.snapshot_eq silent).mp novel
  have fresh := (GeneralRebaseInstallNovelty279.fresh_iff_edge before effect).mp child
  obtain ⟨e,new,old⟩ := fresh
  exact (projected_iff source checked closed path (.tail path actual)).mpr ⟨e,old,new⟩

def EdgeFreeModelCover (r : Registry) (root : Occurrence roles) (start : State roles)
    (tests : List Assignment) : Prop :=
  ∀ before, B4Target.Steps (Actual r root) start before → ∀ effect : Effect roles,
    GeneralNominalVersionedMixedKernel234.Installable (registry r) before effect →
    ¬ GeneralNominalVersionedMixedKernel234.Committed before effect.plan →
    Actual r root before (install before effect) →
    ¬ FreshChild before effect.plan →
    ∃ m ∈ tests, Models before m ∧ ¬ Models (install before effect) m

theorem joined_cover (source : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r) (closed : ClosedArguments (registry r))
    (tests : List Assignment) (testCover : EdgeFreeModelCover r root start tests) :
    ∃ edgeFacts : List (Edge roles),
      Covers r root start (edgeFacts.map Fact.edge ++ tests.map Fact.removed) := by
  obtain ⟨edges,available⟩ := finite_full_edges source checked closed
  refine ⟨edges,?_⟩
  intro n before path effect enabled novel actual
  classical
  by_cases fresh : FreshChild before effect.plan
  · obtain ⟨e,new,absent⟩ := (GeneralRebaseInstallNovelty279.fresh_iff_edge before effect).mp fresh
    have member := (available e).mpr ⟨_,.tail (uncount path) actual,new⟩
    exact ⟨.edge e,List.mem_append_left _ (List.mem_map.mpr ⟨e,member,rfl⟩),absent,new⟩
  · obtain ⟨m,test,beforeOK,afterNo⟩ := testCover before (uncount path) effect enabled novel actual fresh
    exact ⟨.removed m,List.mem_append_right _ (List.mem_map.mpr ⟨m,test,rfl⟩),consumed_model beforeOK afterNo⟩

theorem accessible_if_tests_cover (source : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r) (closed : ClosedArguments (registry r))
    (tests : List Assignment) (testCover : EdgeFreeModelCover r root start tests) :
    Acc (fun next before => Actual r root before next) start := by
  obtain ⟨_edgeFacts,cover⟩ := joined_cover source checked closed tests testCover
  exact accessible_from cover ⟨start,source,.refl⟩

end Yulang.GeneralRebaseFullEdgeProgress279
