import Yulang.GeneralDictionaryVersionedGap206Feedback234
import Yulang.GeneralNominalVersionedInstalledEvidenceAt233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206Selected234
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 GeneralDictionaryVersionedGap206Install233
open GeneralNominalVersionedJournal232 GeneralNominalCenters CommonNominalFullCarrier

theorem raw_sites : installed.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] :=
  (GeneralNominalVersionedTerminal232.raw_eq children_empty).trans rfl

theorem centers : installed.core.sites = [rootSite snapshot.seed root] :=
  (GeneralNominalVersionedTerminal232.sites_eq children_empty).trans rfl

theorem frame : GeneralNominalVersionedEvidence231.Frame registry installed.core root 37
    (GeneralNominalVersionedInstallation231.replayPlan plan) :=
  GeneralNominalVersionedInstalledEvidence233.frame rfl installed_model

theorem frame_plan {candidate : Plan roles}
    (framed : GeneralNominalVersionedEvidence231.Frame registry installed.core root key candidate) :
    candidate = GeneralNominalVersionedInstallation231.replayPlan plan :=
  GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centers framed frame

theorem known : ¬ GeneralNominalState.RootPending installed.core.erased.current.context.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩

theorem survivor : GeneralNominalVersionedCandidates231.Survivor registry installed.core.erased.current.context root 37 [] := by
  refine ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[((1 : Fin 3),(1 : Fin 3))],rfl,frame.prepared,?_⟩
  unfold GeneralNominalVersionedCandidates231.children GeneralNominalVersionedFrame231.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem unique : GeneralNominalVersionedCandidates231.Unique registry installed.core.erased.current.context root 37 [] := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,identity,_⟩ := other
  cases List.mem_singleton.mp visible
  have same : key = 37 := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem scalar_no_edge (last : GeneralNominalRecursiveInspection.Origin) :
    ¬ GeneralNominalVersionedCycles232.Edge installed (.source 1) last := by
  rintro ⟨parent,test,index,headed,equal,_⟩
  have same := equal model installed_model
  obtain ⟨actual,seen⟩ := same.2.1
  have value := same.2.2 _ actual (.source 1) seen
  have shape := (headed model installed_model).2 actual seen
  change Equivalent (.base .int) actual at value
  cases test with
  | scalar => exact Fin.elim0 index
  | nominal name count =>
    obtain ⟨values,_,head⟩ := shape
    exact GeneralNominalPeelingOrigins.base_not_nominal .int name values (subtype_trans value.1 head.1)
  | structural kind =>
    obtain ⟨values,length,head⟩ := shape
    exact GeneralNominalCenteredHeadMatPairCycles.scalar_no_shape length
      ⟨subtype_trans value.1 head.1,subtype_trans head.2 value.2⟩

theorem scalar_acyclic : ¬ GeneralNominalVersionedCycles232.Cyclic installed (.source 1) := by
  rintro ⟨⟨last,edge,_⟩,_⟩
  exact scalar_no_edge last edge


theorem no_raw_edge (first last : Fin 3) : ¬ GeneralNominalMixedRecurrence.Edge installed.core.erased.current.context.state first last := by
  rintro (⟨kind,_,_,_⟩ | argument)
  · exact Fin.elim0 kind
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model installed_model.1.1
    cases recorded

theorem no_raw_recurs (slot : Fin 3) : ¬ GeneralNominalCycleK2.RecursAt installed.core.erased.current.context.state slot := by
  rintro (⟨child,edge,_⟩ | ⟨⟨child,edge,_⟩,_⟩)
  · exact no_raw_edge slot child (GeneralNominalCycleK2.direct_edge_sound edge)
  · exact no_raw_edge slot child edge

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady installed root := by
  refine ⟨⟨_,centers ▸ List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  rw [centers] at one two
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry installed root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old
      exact no_raw_recurs slot cycle
    · exact scalar_acyclic cycle
    · rw [centers] at present
      cases List.mem_singleton.mp present; exact scalar_acyclic cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
      exact no_raw_recurs visited.1 cycle
    · cases frame_plan framed
      have inspection : (GeneralNominalCenteredSteps.inspection (GeneralNominalVersionedInstallation231.replayPlan plan)).tests = [(.source 1,.scalar .int)] := by
        unfold GeneralNominalCenteredSteps.inspection
        simp only [GeneralNominalVersionedInstallation231.replayPlan,GeneralNominalVersionedTransport231.extendedPlan,GeneralNominalVersionedTransport231.extendedPacket]
        rw [GeneralDictionaryOrdinaryTransport.inspectMany_extended]
        exact GeneralDictionaryDefaultGap206Local.inspection_exact
      rw [inspection] at member
      cases List.mem_singleton.mp member
      exact scalar_acyclic cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible; exact unprepared frame.prepared
    · exact unclosed administrative_ready

theorem equal_outputs (assignment : GeneralNominalCommonBridge.Assignment) (focus) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs installed.core focus assignment := by
  intro first one last two _
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp one
  rw [raw_sites] at present
  cases List.mem_singleton.mp present
  cases List.mem_singleton.mp within
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp two
  rw [raw_sites] at present
  cases List.mem_singleton.mp present
  cases List.mem_singleton.mp within
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem selected : GeneralNominalVersionedSourceBoundary232.Local registry installed root (.selected 37 []) := by
  apply GeneralNominalVersionedSourceBoundary232.local_iff.mpr
  apply GeneralNominalVersionedBoundary232.local_iff.mpr
  apply GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe unique installed_model frame
    (GeneralNominalVersionedInstalledEvidence233.ready rfl children_empty)
    (GeneralNominalVersionedInstalledEvidence233.replay_holds installed_model)
    (GeneralNominalVersionedInstalledEvidence233.class_effects installed_model)
  exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict installed_model
    (fun focus _ => equal_outputs model focus) (equal_outputs model root)

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) registry installed root :=
  GeneralNominalVersionedInstalledEvidenceAt233.source_evidenceAt rfl rfl children_empty rfl
    (by intro site member; cases List.mem_singleton.mp member; rfl) selected

end Yulang.GeneralDictionaryVersionedGap206Selected234
