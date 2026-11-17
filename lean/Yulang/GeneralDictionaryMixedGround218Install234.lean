import Yulang.GeneralDictionaryMixedGround218Frame234
import Yulang.GeneralNominalVersionedMixedKernelCache234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218Install234
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install
open GeneralDictionaryMixedGround218Packet234 (initial initial_model packet_holds)
open GeneralDictionaryMixedGround218Frame234
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalVersionedMixedKernel234

noncomputable def effect : Effect roles :=
  ⟨registry,initial.core,plan,frame,children_eq ▸ unique,ready⟩

noncomputable abbrev installed := install initial effect

theorem requests_empty_after (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests installed.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change site ∈ [GeneralNominalDemandMerging.pointSite root] ++ GeneralNominalVersionedChildren232.rawSites plan at present
  rcases List.mem_append.mp present with old | new
  · cases List.mem_singleton.mp old
    cases within
  · obtain ⟨center,member,rfl⟩ := List.mem_map.mp new
    have child : center.occurrence ∈ GeneralNominalVersionedFrame231.children packet := by
      rw [← GeneralNominalVersionedChildren232.emitted_occurrences plan]
      exact List.mem_map.mpr ⟨center,member,rfl⟩
    rw [children_eq,children_exact] at child
    have same := List.mem_singleton.mp child
    change output ∈ center.occurrence.demand.outputs at within
    rw [same] at within
    cases within

theorem classes : GeneralNominalVersionedEffects231.ClassEffects initial.core root plan model :=
  (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr (effects model)

theorem live : effect.Live installed.core model := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor <;> intro output member <;> simp [requests_empty_after] at member

theorem common : InstallationModels initial effect model :=
  ⟨initial_model,packet_holds,⟨GeneralNominalVersionedPlans231.head_models packet_holds,classes⟩,
    live,(by intro _ member; cases member),(by intro _ member; cases member)⟩

theorem frame_plan {candidate : GeneralNominalCenters.Plan roles} {key}
    (framed : GeneralNominalVersionedEvidence231.Frame registry initial.core root key candidate) : candidate = plan := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = context := framed.context_eq
  have declEq : decl = declaration := parent_only framed.visible framed.role_eq
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
  have inputSame : input = GeneralNominalCenters.rootSite snapshot.seed root := List.mem_singleton.mp framed.center_recorded
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(6,6)] = bounds := Option.some.inj framed.located
  subst bounds; rfl

theorem positions : GeneralNominalVersionedCycles232.Safe initial plan :=
  ⟨GeneralDictionaryGroundCopy218Install.installable.positions.1,fun entry _ => acyclic entry.1⟩

theorem installable : Installable registry initial effect := by
  refine ⟨rfl,rfl,safe,?_,?_,?_,positions,?_,model,common⟩
  · exact GeneralNominalVersionedMixedObservations233.legacy_cache
      (GeneralDictionaryDefaultCache208.initial_valid context root)
  · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
    rw [GeneralDictionaryMixedGround218Packet234.emitted_schema]
  · intro packet member
    cases member
  · intro candidate input framed
    change GeneralNominalVersionedEvidence231.Frame registry initial.core root candidate.packet.declaration.id candidate at framed
    cases frame_plan framed
    exact positions

theorem novel : ¬ Committed initial plan := by
  intro committed
  have edge := committed.2 childSite.occurrence (by change childSite.occurrence ∈ GeneralNominalVersionedFrame231.children packet; rw [children_eq,children_exact]; exact List.mem_singleton_self _)
  cases edge

theorem step : Step registry root initial installed := ⟨root,.root,.install effect installable novel⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root installed :=
  ⟨initial,GeneralDictionaryMixedGround218Packet234.initial_source,.tail .refl step⟩

theorem installed_model : Models installed model := (install_models rfl).mpr common

theorem generated_child : GeneralNominalSaturationState.Generated installed.core.erased.current root childSite.occurrence :=
  GeneralNominalVersionedInstallProperties232.children_generated .root
    (by change childSite.occurrence ∈ GeneralNominalVersionedFrame231.children packet; rw [children_eq,children_exact]; exact List.mem_singleton_self _)
end Yulang.GeneralDictionaryMixedGround218Install234
