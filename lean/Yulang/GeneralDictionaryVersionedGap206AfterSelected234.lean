import Yulang.GeneralDictionaryVersionedGap206After234
import Yulang.GeneralNominalVersionedInstalledEvidenceAt233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206AfterSelected234
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 GeneralDictionaryVersionedGap206Install233
open GeneralDictionaryVersionedGap206Feedback234 (feedback)
open GeneralDictionaryVersionedGap206After234 (currentPlan)
open GeneralNominalVersionedJournal232 GeneralNominalCenters CommonNominalFullCarrier

theorem raw_sites : feedback.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] :=
  GeneralDictionaryVersionedGap206Selected234.raw_sites

theorem centers : feedback.core.sites = [rootSite snapshot.seed root] :=
  GeneralDictionaryVersionedGap206Selected234.centers

theorem frame : GeneralNominalVersionedEvidence231.Frame registry feedback.core root 37 currentPlan :=
  GeneralDictionaryVersionedGap206After234.frame

theorem frame_plan {candidate : Plan roles}
    (framed : GeneralNominalVersionedEvidence231.Frame registry feedback.core root key candidate) :
    candidate = currentPlan :=
  GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centers framed frame

theorem known : ¬ GeneralNominalState.RootPending feedback.core.erased.current.context.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩

theorem survivor : GeneralNominalVersionedCandidates231.Survivor registry feedback.core.erased.current.context root 37 [] := by
  refine ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[((1 : Fin 3),(1 : Fin 3))],rfl,frame.prepared,?_⟩
  unfold GeneralNominalVersionedCandidates231.children GeneralNominalVersionedFrame231.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem unique : GeneralNominalVersionedCandidates231.Unique registry feedback.core.erased.current.context root 37 [] := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,identity,_⟩ := other
  cases List.mem_singleton.mp visible
  have same : key = 37 := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem scalar_no_edge (last : GeneralNominalRecursiveInspection.Origin) :
    ¬ GeneralNominalVersionedCycles232.Edge feedback (.source 1) last := by
  rintro ⟨parent,test,index,headed,equal,_⟩
  have same := equal model GeneralDictionaryVersionedGap206After234.model_retained
  obtain ⟨actual,seen⟩ := same.2.1
  have value := same.2.2 _ actual (.source 1) seen
  have shape := (headed model GeneralDictionaryVersionedGap206After234.model_retained).2 actual seen
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

theorem scalar_acyclic : ¬ GeneralNominalVersionedCycles232.Cyclic feedback (.source 1) := by
  rintro ⟨⟨last,edge,_⟩,_⟩
  exact scalar_no_edge last edge


theorem no_raw_edge (first last : Fin 3) : ¬ GeneralNominalMixedRecurrence.Edge feedback.core.erased.current.context.state first last := by
  rintro (⟨kind,_,_,_⟩ | argument)
  · exact Fin.elim0 kind
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model GeneralDictionaryVersionedGap206After234.model_retained.1.1
    cases recorded

theorem no_raw_recurs (slot : Fin 3) : ¬ GeneralNominalCycleK2.RecursAt feedback.core.erased.current.context.state slot := by
  rintro (⟨child,edge,_⟩ | ⟨⟨child,edge,_⟩,_⟩)
  · exact no_raw_edge slot child (GeneralNominalCycleK2.direct_edge_sound edge)
  · exact no_raw_edge slot child edge

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady feedback root := by
  refine ⟨⟨_,centers ▸ List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  rw [centers] at one two
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry feedback root := by
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
      have inspection : (GeneralNominalCenteredSteps.inspection currentPlan).tests = [(.source 1,.scalar .int)] := by
        unfold GeneralNominalCenteredSteps.inspection
        simp only [GeneralDictionaryVersionedGap206After234.currentPlan,GeneralNominalVersionedInstallation231.replayPlan,GeneralNominalVersionedTransport231.extendedPlan,GeneralNominalVersionedTransport231.extendedPacket]
        rw [GeneralDictionaryOrdinaryTransport.inspectMany_extended,GeneralDictionaryOrdinaryTransport.inspectMany_extended]
        exact GeneralDictionaryDefaultGap206Local.inspection_exact
      rw [inspection] at member
      cases List.mem_singleton.mp member
      exact scalar_acyclic cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible; exact unprepared frame.prepared
    · exact unclosed administrative_ready

theorem equal_outputs (assignment : GeneralNominalCommonBridge.Assignment) (focus) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs feedback.core focus assignment := by
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

theorem selected : GeneralNominalVersionedSourceBoundary232.Local registry feedback root (.selected 37 []) := by
  apply GeneralNominalVersionedSourceBoundary232.local_iff.mpr
  apply GeneralNominalVersionedBoundary232.local_iff.mpr
  apply GeneralNominalVersionedDiagnosticLaws232.selected_of_model safe unique GeneralDictionaryVersionedGap206After234.model_retained frame
    GeneralDictionaryVersionedGap206After234.ready
    (GeneralDictionaryVersionedGap206After234.holds model GeneralDictionaryVersionedGap206After234.model_retained)
    (GeneralDictionaryVersionedGap206After234.effects model GeneralDictionaryVersionedGap206After234.model_retained)
  exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict GeneralDictionaryVersionedGap206After234.model_retained
    (fun focus _ => equal_outputs model focus) (equal_outputs model root)

theorem edges_empty : feedback.core.erased.current.edges = [] := by
  change [] ++ GeneralNominalVersionedChildren232.edges plan = []
  unfold GeneralNominalVersionedChildren232.edges
  rw [children_empty]
  rfl

theorem generated_only (generated : GeneralNominalSaturationState.Generated feedback.core.erased.current root focus) : focus = root :=
  GeneralNominalVersionedInstalledEvidenceAt233.generated_only edges_empty
    (by intro site member; rw [raw_sites] at member; cases List.mem_singleton.mp member; rfl) generated

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) registry feedback root := by
  intro assignment valid demand key children dictionaries reached _stable _childStable chosen given
  have same : demand = root := reached.elim id generated_only
  subst demand
  have same := B4TargetV8.local_functional chosen selected
  cases same
  cases given
  exact GeneralDictionaryVersionedGap206After234.evidence assignment valid

end Yulang.GeneralDictionaryVersionedGap206AfterSelected234
