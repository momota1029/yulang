import Yulang.GeneralLatePeerFinalPeerPlan311
import Yulang.GeneralVersionedPeerChoice311
import Yulang.GeneralPeerInstallationOrder311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 21000000
namespace Yulang.GeneralLatePeerCurrent311
open GeneralLatePeerSource311 (root registry compiled checked initial_source receiver)
open GeneralLatePeerRoot311 (direct branch z direct_output)
open GeneralLatePeerRoutePlan311 (child child_args)
open GeneralLatePeerRouteInstall311 (emitted)
open GeneralLatePeerDirectInstall311 (recorded reached_recorded)
open GeneralLatePeerMerge311 (final reached alias same_inputs context_same raw_sites center_sites identity_before)
open GeneralLatePeerFinalPeerPlan311 (plan packet report ctx two body)
open GeneralLatePeerFresh311 (Pool)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalVersionedEvidence231 (Frame Certificate Evidence)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff EqualOutputs)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralGeneratedNestedSource299 (model)
open GeneralSourceDictionaries (Occurrence)
open CommonNominalFullCarrier (Equivalent subtype_refl)

abbrev rp := GeneralLatePeerRouteInstall311.packet
abbrev dp := GeneralLatePeerDirectPlan311.packet

theorem inhabited : Models final model := (GeneralLatePeerMerge311.models _).mpr GeneralLatePeerRouteInstall311.inhabited

theorem pool : Pool ctx.state [branch.occurrence.identity,direct.occurrence.identity,root.identity] := by
  change Pool final.core.erased.current.context.state _
  rw [context_same]
  apply GeneralLatePeerFresh311.extend_pool recorded.core.erased.current.context rp
    GeneralLatePeerRouteInstall311.ctx_packet GeneralLatePeerRouteInstall311.pool
  have bound : ∀ n ∈ (atoms rp).flatMap GeneralNominalState.atomSources, n ≤ 2 := by
    unfold atoms
    rw [show rp = GeneralNominalVersionedTransport231.extendedPacket
      GeneralLatePeerRouteInstall311.rs GeneralLatePeerRouteInstall311.ats GeneralLatePeerRouteInstall311.owned
      GeneralLatePeerRoutePlan311.middlePacket from congrArg GeneralNominalCenters.Plan.packet GeneralLatePeerRouteInstall311.plan_flat,
      GeneralNominalVersionedTransport231.packet_bindings,GeneralLatePeerRoutePlan311.bindings]
    change ∀ n ∈ ((GeneralNominalAllocation.cross [(0, (2, 2))] ++
      GeneralNominalVersionedAllocation231.merges _ _ _ _ [(0,(2,2))]) ++
      GeneralNominalRecursiveInspection.selfChecks _ (GeneralNominalPacketSupport.report _)).flatMap
      GeneralNominalState.atomSources, n ≤ 2
    change ∀ n ∈ ((GeneralNominalAllocation.cross [(0, (2, 2))] ++
      GeneralNominalVersionedAllocation231.merges _ _ _ _ [(0,(2,2))]) ++
      GeneralNominalRecursiveInspection.selfChecks _
        (GeneralNominalRecursiveCandidates.report
          (GeneralDictionaryOrdinaryTransport.extend GeneralGeneratedNestedSource299.context
            GeneralLatePeerRouteInstall311.rs GeneralLatePeerRouteInstall311.ats GeneralLatePeerRouteInstall311.owned)
          GeneralLatePeerSource311.route [(1,1)])).flatMap GeneralNominalState.atomSources, n ≤ 2
    rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
      GeneralDictionaryOrdinaryTransport.selfChecks_report,GeneralLatePeerRoutePlan311.middle_report]
    decide +kernel
  exact fun atom listed n hit => bound n (List.mem_flatMap.mpr ⟨atom,listed,hit⟩)

theorem fresh (bs : GeneralNominalAllocation.Bindings) :
    GeneralNominalVersionedAllocation231.Fresh ctx.state compiled child.occurrence.identity bs :=
  GeneralLatePeerFresh311.fresh pool compiled child.occurrence.identity (by
    intro mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with atBranch|atDirect|atRoot
    · exact GeneralLatePeerMerge311.child_branch atBranch
    · exact GeneralLatePeerMerge311.child_new atDirect
    · exact GeneralLatePeerMerge311.child_root atRoot) bs

theorem located : GeneralVersionedPeerChoice311.reads ctx child.occurrence = some [(two,two)] := by decide +kernel

theorem known : GeneralLatePeerGuard311.Known final child.occurrence := by
  rintro ⟨i,absent⟩
  exact absent ⟨two,(congrArg Prod.fst (child_args i)).symm,Or.inl (by decide +kernel)⟩

theorem linked : GeneralNominalState.Linked ctx.state (inputs child.occurrence).demand := by
  refine ⟨?_,?_⟩
  · intro i
    change (child.occurrence.demand.arguments i).1 ∈ GeneralNominalState.sources ctx.state ∧
      (child.occurrence.demand.arguments i).2 ∈ GeneralNominalState.sources ctx.state
    rw [child_args]
    exact ⟨GeneralNominalAllocationSupport.slot_source ctx.state two,GeneralNominalAllocationSupport.slot_source ctx.state two⟩
  · intro _ absent; cases absent

theorem prepared : Prepared compiled ctx child.occurrence receiver := by
  refine ⟨⟨rfl,initial_source.metadata.2⟩,linked,[(two,two)],located,fresh _,?_,model,?_⟩
  · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report packet)
    rw [report]; exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralNominalVersionedCandidates231.headModels_packet_iff packet model).mpr
      (GeneralNominalVersionedPlans231.head_models (plan := plan) (GeneralLatePeerFinalPeerPlan311.holds model inhabited))

theorem frame : Frame compiled final.core child.occurrence 2 plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_cons_of_mem _ List.mem_cons_self,rfl,located,prepared⟩
  · change child.observed ∈ emitted.core.erased.current.sites
    rw [raw_sites]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · exact GeneralLatePeerMerge311.child_seen

theorem both_alias : Alias final.core.erased.current direct.occurrence.identity child.occurrence.identity := .symm alias

theorem admin : GeneralNominalVersionedDiagnostic232.AdministrativeReady final child.occurrence := by
  refine ⟨⟨child,frame.center_recorded,rfl⟩,?_⟩
  intro a one occ b last eq
  change a ∈ emitted.core.sites at one
  change b ∈ emitted.core.sites at last
  rw [center_sites] at one last
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one last
  have identity := congrArg Occurrence.identity occ
  rcases one with rfl|rfl|rfl|rfl
  · exact False.elim (GeneralLatePeerMerge311.child_root identity.symm)
  · exact False.elim (GeneralLatePeerMerge311.child_new identity.symm)
  · exact False.elim (GeneralLatePeerMerge311.child_branch identity.symm)
  · rcases last with rfl|rfl|rfl|rfl
    · cases eq.1
    · exact alias
    · cases eq.1
    · exact .refl _

theorem request {d : Occurrence roles} (out : GeneralSourceState.Output) (member : out ∈ requests final.core d) :
    out = ⟨1,z⟩ := by
  obtain ⟨s,seen,_,inside⟩ := mem_requests_iff.mp member
  change s ∈ emitted.core.erased.current.sites at seen
  rw [raw_sites] at seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl|rfl|rfl
  · cases inside
  · exact List.mem_singleton.mp (direct_output ▸ inside)
  · cases inside
  · cases inside

theorem equal_outputs (d : Occurrence roles) (m : Assignment) : EqualOutputs final.core d m := by
  intro a one b two _
  cases request a one
  cases request b two
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem current_z (m : Assignment) (valid : Models final m) : Equivalent (m z).1 (.base .int) :=
  ((GeneralLatePeerDirectInstall311.models m).mp
    ((GeneralLatePeerRouteInstall311.models m).mp ((GeneralLatePeerMerge311.models m).mp valid))).2

theorem classes (m : Assignment) (valid : Models final m) :
    GeneralNominalVersionedEffects231.ClassEffects final.core child.occurrence plan m := by
  refine ⟨?_,equal_outputs _ _⟩
  intro out listed picked comes
  cases request out listed
  have same : picked = .explicit body := (Option.some.inj comes).symm
  subst picked
  intro a seen
  cases List.mem_singleton.mp seen
  exact current_z m valid

theorem clear (d : Occurrence roles) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict final d :=
  GeneralNominalVersionedMergedConflict232.models_exclude_conflict inhabited
    (fun focus _ => equal_outputs focus model) (equal_outputs d model)

theorem picked : Local registry final child.occurrence (.selected 2 (GeneralLatePeerGuard311.children plan)) :=
  GeneralLatePeerGuard311.select reached frame known rfl inhabited admin
    (GeneralLatePeerFinalPeerPlan311.holds model inhabited) (classes model inhabited) (clear _)

theorem leaf_certificate (m : Assignment) (valid : Models final m) :
    Certificate compiled final.core m child.occurrence 2 [] plan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics frame
    GeneralLatePeerFinalPeerPlan311.no_children.symm (GeneralLatePeerFinalPeerPlan311.holds m valid)
    (GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reached frame) (classes m valid)

theorem leaf_evidence (m : Assignment) (valid : Models final m) :
    Evidence compiled final.core m child.occurrence (.node 2 []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨_,leaf_certificate m valid⟩

end Yulang.GeneralLatePeerCurrent311
