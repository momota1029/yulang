import Yulang.GeneralDictionaryMixedGround218PointSafety235
import Yulang.GeneralNominalVersionedMixedCommon235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218PointInstall235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (declaration declaration_checked model parent_only clause)
open GeneralDictionaryMixedGround218Point235
open GeneralDictionaryMixedGround218PointPacket235 (plan packet packet_holds context_eq bindings_exact)
open GeneralDictionaryMixedGround218PointFrame235 (frame prepared)
open GeneralDictionaryMixedGround218PointSafety235 (known safe acyclic)
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232 GeneralNominalVersionedMixedKernel234

theorem children_eq : GeneralNominalVersionedFrame231.children packet =
    [GeneralDictionaryGroundCopy218Reinstall.newChild.occurrence] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralDictionaryGroundCopy218Install.canonical_declaration]
  change [GeneralNominalVersionedFrame231.clauseChild packet clause _] = _
  apply congrArg List.singleton
  apply congrArg (fun arguments : Fin 2 → GeneralSourceState.Interval =>
    (⟨GeneralNominalCenters.fresh 7 0 0 6 0 0,⟨1,arguments,[],by intro _ h; cases h⟩⟩ : GeneralSourceDictionaries.Occurrence roles))
  funext i
  change Fin 2 at i
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl | rfl
  · change (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (GeneralNominalPacketSupport.capture GeneralDictionaryGroundCopy218Reinstall.newPacket).inputs 0
    rw [GeneralDictionaryMixedGround218PointPacket235.capture 0 (Or.inl rfl),GeneralDictionaryGroundCopy218Reinstall.capture_zero]
    rfl
  · change (GeneralNominalVersionedFrame231.capture packet).inputs 1 = (GeneralNominalPacketSupport.capture GeneralDictionaryGroundCopy218Reinstall.newPacket).inputs 1
    rw [GeneralDictionaryMixedGround218PointPacket235.capture 1 (Or.inr rfl),GeneralDictionaryGroundCopy218Reinstall.capture_one]
    rfl

theorem unique : GeneralNominalVersionedCandidates231.Unique registry point.core.erased.current.context root 0
    (GeneralNominalVersionedFrame231.children packet) := by
  rw [← context_eq]
  have survivor : GeneralNominalVersionedCandidates231.Survivor registry packet.context root 0
      (GeneralNominalVersionedFrame231.children packet) :=
    ⟨context_eq.symm ▸ known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[(6,6)],rfl,prepared,rfl⟩
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases parent_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready point.core root plan :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,source_checked⟩ reachable frame

noncomputable def effect : Effect roles := ⟨registry,point.core,plan,frame,unique,ready⟩
noncomputable abbrev installed := install point effect

theorem requests_empty (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests point.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  have old := (GeneralNominalVersionedRefresh232.reobserve_requests _ _).mp member
  rw [GeneralDictionaryMixedGround218Install234.requests_empty_after] at old
  cases old

theorem classes (given : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects point.core root plan given := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor <;> intro output member <;> simp [requests_empty] at member

theorem common : InstallationModels point effect model :=
  (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,source_checked⟩ reachable rfl rfl).mpr
    ⟨point_model,packet_holds,classes model⟩

theorem installable : Installable registry point effect := by
  refine ⟨rfl,rfl,safe,?_,?_,?_,?_,?_,model,common⟩
  · exact GeneralNominalVersionedMixedKernelCache234.reachable_cache
      (GeneralNominalVersionedMixedSourceBoundary234.reachable_compiled reachable)
  · exact GeneralNominalVersionedMixedReady235.materialized reachable frame
  · intro prior member _
    cases List.mem_singleton.mp member
    rfl
  · refine ⟨GeneralNominalCenteredInspection.plan_complete plan ?_,fun entry _ => acyclic entry.1⟩
    exact frame.located
  · intro candidate _ _
    refine ⟨?_,fun entry _ => acyclic entry.1⟩
    apply GeneralNominalCenteredInspection.plan_complete
    rename_i framed
    have located := framed.located
    rw [← framed.occurrence_eq,←candidate.input_exact] at located
    exact located

theorem novel : ¬ Committed point plan := by
  intro committed
  have member := committed.2 GeneralDictionaryGroundCopy218Reinstall.newChild.occurrence
    (by rw [children_eq]; exact List.mem_singleton_self _)
  have edges : point.core.erased.current.edges = [(root,GeneralDictionaryGroundCopy218Install.childSite.occurrence)] := by
    change GeneralNominalVersionedChildren232.edges GeneralDictionaryGroundCopy218Install.plan = _
    unfold GeneralNominalVersionedChildren232.edges
    rw [GeneralDictionaryMixedGround218Frame234.children_eq,GeneralDictionaryGroundCopy218Install.children_exact]
    rfl
  rw [edges] at member
  exact GeneralDictionaryGroundCopy218Reinstall.different_child (congrArg Prod.snd (List.mem_singleton.mp member))

theorem step : Step registry root point installed := ⟨root,.root,.install effect installable novel⟩

theorem reachable_installed : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
    sourceRegistry root installed := by
  obtain ⟨start,initial,path⟩ := GeneralDictionaryMixedGround218Point235.reachable
  exact ⟨start,initial,.tail path step⟩

theorem installed_model : Models installed model := (install_models rfl).mpr common

end Yulang.GeneralDictionaryMixedGround218PointInstall235
