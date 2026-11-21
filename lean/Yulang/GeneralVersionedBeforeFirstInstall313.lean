import Yulang.GeneralVersionedRawReportDomain313
import Yulang.GeneralVersionedSiteOrigins312
import Yulang.GeneralVersionedHeadFromSharing313

set_option backward.isDefEq.respectTransparency false
/-! Before the first real installation the full journal has exactly the
source models, irrespective of lawful refresh/reobservation/equality. The
point source condition is part of the existing source boundary. -/
namespace Yulang.GeneralVersionedBeforeFirstInstall313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedModelSupport237 (Support Observation observation_models)
open GeneralVersionedTraceDomain313 (seed)
open GeneralNominalState (sources)
open GeneralNominalCommonBridge (Assignment)

abbrev source (s : State roles) := s.core.erased.source

theorem no_child_site {s : State roles} (actual : Reachable registry root s) (empty : s.plans = [])
    (one two : Site roles) (a : one ∈ s.core.sites) (b : two ∈ s.core.sites) : one = two := by
  obtain ⟨ctx,traced⟩ := GeneralVersionedSiteOrigins312.reached actual
  have only (site : Site roles) (member : site ∈ s.core.sites) : site = rootSite ctx.state.seed root := by
    rcases traced.origin site member with first | ⟨prior,found,_⟩
    · exact first
    · rw [empty] at found
      cases found
  exact (only one a).trans (only two b).symm

theorem predecessor {s t : State roles}
    (actual : Reachable registry root s) (step : Step (GeneralNominalCenteredHeadAllocEncoding.registry registry) root s t)
    (empty : t.plans = []) : s.plans = [] ∧ Observation s t := by
  have beforeEmpty : s.plans = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro p inside
    have still := (GeneralNominalVersionedMixedGrowth234.step step).plans inside
    rw [empty] at still
    cases still
  refine ⟨beforeEmpty,?_⟩
  rcases GeneralNominalVersionedMixedProgressSplit236.split actual step with update|⟨effect,_,_,rfl⟩
  · cases update with
    | refresh context certificate _ _ _ _ => exact .refresh _ context certificate
    | reobserve revision certificate _ => exact .reobserve _ revision certificate
    | equate first last _ _ equal _ => exact .equate _ first last equal
    | merge first last a b _ new =>
      have same := no_child_site actual beforeEmpty first last a b
      rw [same] at new
      exact False.elim (new (.refl _))
  · cases empty

theorem models_exact {s : State roles} (actual : Reachable registry root s)
    (empty : s.plans = []) (m : Assignment) :
    Models s m ↔ GeneralNominalState.Models (source s).state m := by
  obtain ⟨start,formed,steps⟩ := actual
  induction steps with
  | refl =>
    obtain ⟨legacy,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩ := formed
    change Models (GeneralNominalVersionedJournal232.initial ctx root) m ↔ GeneralNominalState.Models ctx.state m
    rw [GeneralNominalVersionedJournal232.initial_models]
    exact ⟨And.left,fun valid => ⟨valid,GeneralNominalCenters.point_root_holds _ _ point m⟩⟩
  | tail prior step ih =>
    obtain ⟨beforeEmpty,observe⟩ := predecessor ⟨start,formed,prior⟩ step empty
    have eq := GeneralNominalVersionedMixedGrowth234.step_source step
    rw [show source _ = source _ from eq]
    exact (observation_models observe m).trans (ih beforeEmpty)

theorem support_initial {s : State roles} (actual : Reachable registry root s) (empty : s.plans = []) :
    Support s (sources (source s).state) := by
  intro m n agree
  have more : GeneralNominalSemanticRawFrame236.sources (source s).state ⊆ sources (source s).state :=
    GeneralNominalSemanticRawFrame236.contained (source s).state
  exact (models_exact actual empty m).trans ((GeneralNominalSemanticRawFrame236.source_models_same _
    (fun k h => agree k (more h))).trans (models_exact actual empty n).symm)

theorem source_small {s : State roles} {id : Nat} (actual : Reachable registry root s)
    (member : id ∈ sources (source s).state) : id ≤ seed s := by
  obtain ⟨start,⟨legacy,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩,steps⟩ := actual
  have old := GeneralNominalVersionedMixedGrowth234.steps_source steps
  change id ∈ sources s.core.erased.source.state at member
  rw [old] at member
  rw [show seed s = ctx.state.seed from (GeneralNominalVersionedMixedGrowth234.steps steps).seed]
  exact formation.below_seed _ member

theorem source_slot_clean {s : State roles} {id : Nat} (actual : Reachable registry root s) (empty : s.plans = [])
    (member : id ∈ GeneralNominalVersionedMixedAdministrative236.support s) : id ≤ seed s := by
  rcases GeneralVersionedTraceDomain313.reached actual _ member with small|⟨p,found,_⟩
  · exact small
  · rw [empty] at found
    cases found

theorem center_small {s : State roles} (actual : Reachable registry root s) (empty : s.plans = [])
    (registered : site ∈ s.core.sites) (i : Fin (roles site.occurrence.demand.role).arity) :
    site.center i ≤ seed s := by
  obtain ⟨start,⟨legacy,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩,steps⟩ := actual
  have reached : Reachable registry root s := ⟨_,⟨_,⟨ctx,labels,formation,point,ground,cover,rfl⟩,rfl⟩,steps⟩
  have origins := GeneralVersionedSiteOrigins312.trace steps
  rcases origins.origin site registered with same|⟨p,found,_⟩
  · subst site
    rw [GeneralNominalCenters.point_center ctx.state.seed root i (point i)]
    rw [show seed s = ctx.state.seed from (GeneralNominalVersionedMixedGrowth234.steps steps).seed]
    exact formation.below_seed _ (formation.linked.1 i).1
  · rw [empty] at found
    cases found

end Yulang.GeneralVersionedBeforeFirstInstall313
