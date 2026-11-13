import Yulang.GeneralNominalCenteredBoundary

/-! Exact point-source initialization and support agreement. These statements
concern the initial state; later compound names require model extension. -/
namespace Yulang.GeneralNominalCenteredPointSource
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls}

def Point (root : Occurrence roles) : Prop :=
  ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2

theorem supplied_site_unique (site : Site roles) (named : site.PointNames)
    (point : Point site.occurrence) (seed : Nat) : site = rootSite seed site.occurrence := by
  cases site with
  | mk occurrence center =>
    congr
    funext index
    exact (named index (point index)).trans (point_center seed occurrence index (point index)).symm

theorem initial_unique (source : InitialSource registry root state) (point : Point root) :
    ∃ context, GeneralNominalSourceFormation.InitialSource registry context root ∧ state = initial context root := by
  obtain ⟨context,site,formed,same,named,rfl⟩ := source
  subst root
  exact ⟨context,formed,congrArg (initialAt context) (supplied_site_unique site named point _)⟩

theorem initial_models_erase (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (point : Point root) (model : Assignment) :
    Models (initial context root) model ↔ GeneralNominalSaturationState.Models (initial context root).erased.current model :=
  (point_initial_models context root point model).trans (GeneralNominalSaturationState.initial_models context root model).symm

private theorem old_trusted_empty
    (trusted : GeneralNominalSharedSupport.Trusted (GeneralNominalSupport.initial context root) facts readbacks) : facts = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro fact member
  have absent := GeneralNominalSettledSupport.trusted_members (GeneralNominalSharedSupport.trusted_old trusted) fact member
  cases absent

private theorem trusted_empty
    (trusted : GeneralNominalCenteredSupport.Trusted (GeneralNominalSupport.initial context root)
      [rootSite context.state.seed root] [] facts) : facts = [] := by
  cases trusted with
  | source => rfl
  | legacy facts readbacks given => rw [old_trusted_empty given]; rfl
  | input plan support previous member => cases member
  | output plan support previous member => cases member
  | merge first last support previous recorded => cases recorded

theorem initial_ready_iff (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (point : Point root) (identity : Nat) :
    GeneralNominalCenteredSupport.ReadyAt (initial context root).erased
      (initial context root).sourceSites (initial context root).plans identity ↔
      GeneralNominalSharedSupport.ReadyAt (GeneralNominalSupport.initial context root) identity := by
  constructor
  · rintro ⟨test,observation,seen,facts,trusted,snapshot,witness,recorded,sound⟩
    have empty := trusted_empty trusted
    subst facts
    refine ⟨test,observation,seen,[],[],.source,snapshot,witness,recorded,?_⟩
    intro model valid
    apply sound model
    exact ⟨valid.1,by
      intro site member
      cases List.mem_singleton.mp member
      exact point_root_holds _ root point model,by intro fact member; cases member⟩
  · exact GeneralNominalCenteredSupport.legacy_ready

theorem initial_decision_iff (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root focus : Occurrence roles) (point : Point root) :
    DecisionGuard registry (initial context root) focus ↔
      GeneralNominalSharedSupport.DecisionGuard registry (GeneralNominalSupport.initial context root) focus := by
  constructor
  · intro guard
    exact ⟨fun index => (initial_ready_iff context root point _).mp (guard.1 index),
      fun declaration visible role bounds located slot visited =>
        (initial_ready_iff context root point _).mp (guard.2 declaration visible role bounds located slot visited)⟩
  · exact GeneralNominalCenteredSupport.legacy_decision

theorem initial_refresh_erases (context after : GeneralNominalCandidates.Context)
    (root focus : Occurrence roles) (point : Point root)
    (certificate : Refresh (initial context root) after)
    (source : Nat) (member : source ∈ GeneralNominalState.sources context.state)
    (unknown : ¬ GeneralNominalState.Known context.state source)
    (known : GeneralNominalState.Known after.state source)
    (generated : GeneralNominalSaturationState.Generated (initial context root).erased.current root focus) :
    GeneralNominalActualInspectionSteps.Step registry root (initial context root).erased
      (refresh (initial context root) after).erased := by
  exact (refresh_compatible generated certificate
    (fun model valid => certificate.exact model ((initial_models_erase context root point model).mpr valid))
    source member unknown known).2

theorem point_observed (site : Site roles) (point : Point site.occurrence) (named : site.PointNames) :
    site.observed = GeneralNominalDemandMerging.pointSite site.occurrence := by
  unfold Site.observed GeneralNominalDemandMerging.pointSite
  congr 1
  apply congrArg List.ofFn
  funext index
  simp only [point index,ite_true,named index (point index)]

end Yulang.GeneralNominalCenteredPointSource
