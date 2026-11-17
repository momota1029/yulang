import Yulang.GeneralDictionaryMixedGround218PointStable235
import Yulang.GeneralDictionaryMixedGround218PointUniform235
import Yulang.GeneralDictionaryMixedGround218PointChildren235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218RootCommitted235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (plan childSite declaration)
open GeneralDictionaryGroundCopy218Reinstall (newChild)
open GeneralDictionaryGroundCopy218SaturatedParent (contextFor planFor)
open GeneralDictionaryMixedGround218PointStable235 (Sites)
open GeneralNominalCenters GeneralSourceDictionaries GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedKernel234
variable {state : State roles}
theorem frame_plan (sites : Sites state) (allocated reserved atoms)
    (current : state.core.erased.current.context = contextFor allocated reserved atoms) {candidate : Plan roles} {key}
    (framed : GeneralNominalVersionedEvidence231.Frame registry state.core root key candidate) : candidate = planFor allocated reserved atoms := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = contextFor allocated reserved atoms := framed.context_eq.trans current
  have declEq : decl = declaration := GeneralDictionaryGroundCopy218Install.parent_only framed.visible framed.role_eq
  have raw := framed.raw_recorded
  rw [sites.2.1] at raw
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := by
    rcases List.mem_cons.mp raw with yes | raw
    · exact yes
    · rcases List.mem_cons.mp raw with yes | raw
      · have eq := framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
      · have yes := List.mem_singleton.mp raw
        have eq := framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
  have centers := framed.center_recorded
  rw [sites.1] at centers
  change input ∈ [plan.input,childSite,newChild] at centers
  have inputSame : input = plan.input := by
    rcases List.mem_cons.mp centers with yes | centers
    · exact yes
    · rcases List.mem_cons.mp centers with yes | centers
      · have eq := inputEq.trans framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
      · have yes := List.mem_singleton.mp centers
        have eq := inputEq.trans framed.occurrence_eq
        rw [yes] at eq
        have bad := congrArg (fun o : Occurrence roles => o.demand.role) eq
        cases bad
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(6,6)] = bounds := Option.some.inj framed.located
  subst bounds; rfl


theorem requests_empty (sites : Sites state) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests state.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [sites.2.1] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl <;> cases within

theorem classes (sites : Sites state) (candidate : Plan roles) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects state.core focus candidate model := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor <;> intro output member <;> simp [requests_empty sites] at member

theorem frame_holds (sites : Sites state) (allocated reserved atoms)
    (current : state.core.erased.current.context = contextFor allocated reserved atoms)
    (framed : GeneralNominalVersionedEvidence231.Frame registry state.core root key candidate)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    GeneralNominalVersionedPlans231.Holds candidate model := by
  rw [frame_plan sites allocated reserved atoms current framed]
  have raw := valid.1.1
  rw [current] at raw
  exact GeneralDictionaryMixedGround218PointUniform235.packet_holds model raw

theorem frame_committed (sites : Sites state) (allocated reserved atoms)
    (current : state.core.erased.current.context = contextFor allocated reserved atoms)
    (framed : GeneralNominalVersionedEvidence231.Frame registry state.core root key candidate) :
    Committed state candidate := by
  refine ⟨fun model valid => ⟨frame_holds sites allocated reserved atoms current framed model valid,classes sites candidate model⟩,?_⟩
  intro child member
  rw [frame_plan sites allocated reserved atoms current framed,
    GeneralDictionaryMixedGround218PointChildren235.children_eq] at member
  cases List.mem_singleton.mp member
  rw [framed.occurrence_eq,sites.2.2]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem root_committed (sites : Sites state) (allocated reserved atoms)
    (current : state.core.erased.current.context = contextFor allocated reserved atoms)
    (effect : Effect roles) (enabled : Installable registry state effect)
    (focus : effect.plan.packet.site.occurrence = root) : Committed state effect.plan := by
  apply frame_committed sites allocated reserved atoms current
  rw [← focus,← enabled.registry_eq,← enabled.snapshot_eq]
  exact effect.frame

theorem stable (sites : Sites state) (recorded : plan ∈ state.plans)
    (allocated reserved atoms)
    (current : state.core.erased.current.context = contextFor allocated reserved atoms)
    (valid : Models state GeneralDictionaryGroundCopy218Install.model)
    (equalities : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed state) : Stable registry state root :=
  GeneralDictionaryMixedGround218PointStable235.stable sites recorded allocated reserved atoms
    (congrArg GeneralNominalCandidates.Context.state current) valid equalities
    (root_committed sites allocated reserved atoms current)
end Yulang.GeneralDictionaryMixedGround218RootCommitted235

