import Yulang.GeneralLatePeerRouteInstall311
import Yulang.GeneralRebaseMergeRequests264
import Yulang.GeneralVersionedCenteredReplay311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 17500000
namespace Yulang.GeneralLatePeerMerge311
open GeneralLatePeerSource311 (registry compiled root)
open GeneralLatePeerRoot311 (direct branch z direct_output)
open GeneralLatePeerRoutePlan311 (child child_data)
open GeneralLatePeerRouteInstall311 (emitted reached_emitted peer_list plan)
open GeneralLatePeerDirectInstall311 (recorded centers_same)
open GeneralLatePeerFirst311 (centers raw)
open GeneralLatePeerFresh311 (direct_different branch_different distinct_child)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalVersionedAdministrative232 (merge merge_models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open CommonNominalFullCarrier (subtype_refl)
open GeneralNominalCenters (SameInputs)

abbrev final : State roles := merge emitted direct child

theorem ever_emitted : GeneralNominalVersionedChildren232.emitted plan = [child] := by
  change GeneralNominalVersionedChildren232.emitted
    (GeneralNominalVersionedTransport231.extendedPlan _ _ _ GeneralLatePeerRouteInstall311.partially) = _
  rw [GeneralVersionedCenteredReplay311.emitted_extended]
  change GeneralNominalVersionedChildren232.emitted
    (GeneralNominalVersionedTransport231.extendedPlan _ _ _ GeneralLatePeerRoutePlan311.plan) = _
  rw [GeneralVersionedCenteredReplay311.emitted_extended]
  exact GeneralLatePeerRoutePlan311.emitted_sites

theorem center_sites : emitted.core.sites = [GeneralLatePeerRoot311.plan.input,direct,branch,child] := by
  change recorded.core.sites ++ GeneralNominalVersionedChildren232.emitted plan = _
  rw [centers_same,centers,ever_emitted]
  rfl

theorem raw_sites : emitted.core.erased.current.sites =
    [GeneralLatePeerRoot311.packet.site,direct.observed,branch.observed,child.observed] := by
  change recorded.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites plan = _
  rw [GeneralLatePeerRouteInstall311.raw_same,raw]
  unfold GeneralNominalVersionedChildren232.rawSites
  rw [ever_emitted]
  rfl

theorem direct_seen : direct ∈ emitted.core.sites := center_sites ▸ List.mem_cons_of_mem _ List.mem_cons_self
theorem child_seen : child ∈ emitted.core.sites := center_sites ▸
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem child_new : child.occurrence.identity ≠ direct.occurrence.identity := by decide +kernel
theorem child_root : child.occurrence.identity ≠ root.identity := by decide +kernel
theorem child_branch : child.occurrence.identity ≠ branch.occurrence.identity := by decide +kernel

theorem exact_edges : emitted.core.erased.current.edges =
    [(root,direct.occurrence),(root,branch.occurrence),(branch.occurrence,child.occurrence)] := by
  change (GeneralLatePeerFirst311.after.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges GeneralLatePeerDirectPlan311.plan) ++
    GeneralNominalVersionedChildren232.edges plan = _
  rw [GeneralLatePeerFirst311.edges]
  unfold GeneralNominalVersionedChildren232.edges
  rw [GeneralLatePeerDirectPlan311.no_children]
  change ([(root,direct.occurrence),(root,branch.occurrence)] ++ []) ++
    (GeneralNominalVersionedFrame231.children plan.packet).map (fun kid => (branch.occurrence,kid)) = _
  have pe : GeneralNominalVersionedFrame231.children plan.packet = [child.occurrence] := peer_list
  rw [pe]
  rfl

theorem actual_direct : Generated emitted.core.erased.current root direct.occurrence :=
  .child .root (exact_edges ▸ List.mem_cons_self)

theorem actual_child : Generated emitted.core.erased.current root child.occurrence :=
  .child (.child .root (exact_edges ▸ List.mem_cons_of_mem _ List.mem_cons_self))
    (exact_edges ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem direct_input : direct.observed.inputs = [some (.source 2)] := by decide +kernel
theorem peer_input : child.observed.inputs = [some (.source 2)] := by decide +kernel

private theorem same_single_name {a b : GeneralNominalCenters.Site roles}
    (model : Assignment → Prop) (r : a.occurrence.demand.role = b.occurrence.demand.role)
    (ha : a.observed.inputs = [some (.source 2)]) (hb : b.observed.inputs = [some (.source 2)]) :
    SameInputs model a b := by
  refine ⟨r,?_⟩
  rw [ha,hb]
  exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩ .nil

theorem same_role : direct.occurrence.demand.role = child.occurrence.demand.role := by decide +kernel

theorem same_inputs : SameInputs (Models emitted) direct child :=
  same_single_name (a := direct) (b := child) (Models emitted) same_role direct_input peer_input

private theorem no_alias {state : GeneralNominalSaturationState.State roles}
    (empty : state.aliases = []) {a b : Nat} (h : Alias state a b) : a = b := by
  induction h with
  | refl => rfl
  | edge h => rw [empty] at h; cases h
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second

theorem identity_before {a b : Nat} (alias : Alias emitted.core.erased.current a b) : a=b := by
  exact no_alias rfl alias

theorem step : Step compiled root emitted final :=
  ⟨direct.occurrence,actual_direct,.merge direct child direct_seen child_seen same_inputs
    (fun h => child_new (identity_before h).symm)⟩

theorem reached : B4TargetV8.Reachable (boundary roles) registry root final := by
  obtain ⟨first,initial,walk⟩ := reached_emitted
  exact ⟨first,initial,.tail walk step⟩

theorem alias : Alias final.core.erased.current child.occurrence.identity direct.occurrence.identity :=
  .symm (.edge List.mem_cons_self)

theorem no_added_atoms : GeneralNominalDemandMerging.outputAtoms direct.observed child.observed = [] := by
  unfold GeneralNominalDemandMerging.outputAtoms
  change direct.occurrence.demand.outputs.flatMap (fun left => ([] : List GeneralSourceState.Output).flatMap _) = _
  rw [direct_output]
  rfl

theorem context_same : final.core.erased.current.context = emitted.core.erased.current.context := by
  change (⟨GeneralNominalState.extend emitted.core.erased.current.context.state []
    (GeneralNominalDemandMerging.outputAtoms direct.observed child.observed),
    emitted.core.erased.current.context.interpretation⟩ : GeneralNominalCandidates.Context) = _
  rw [no_added_atoms]
  simp only [GeneralNominalState.extend,List.append_nil]

theorem old_request_identity (d : Occurrence roles) (o : GeneralSourceState.Output)
    (p : o ∈ requests emitted.core d) : o = ⟨1,z⟩ ∧ d.identity = direct.occurrence.identity := by
  obtain ⟨s,visible,linked,member⟩ := mem_requests_iff.mp p
  rw [raw_sites] at visible
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl|rfl|rfl|rfl
  · cases member
  · exact ⟨List.mem_singleton.mp (direct_output ▸ member),identity_before linked⟩
  · cases member
  · cases member

theorem direct_seen_raw : direct.observed ∈ final.core.erased.current.sites := by
  change direct.observed ∈ emitted.core.erased.current.sites
  rw [raw_sites]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem inherited : (⟨1,z⟩ : GeneralSourceState.Output) ∈ requests final.core child.occurrence := by
  apply mem_requests_iff.mpr
  refine ⟨direct.observed,direct_seen_raw,alias,?_⟩
  rw [show direct.observed.occurrence.demand.outputs = [⟨1,z⟩] from direct_output]
  exact List.mem_singleton_self _

theorem request_eq (d : Occurrence roles) (away : d.identity ≠ child.occurrence.identity)
    (o : GeneralSourceState.Output) :
    o ∈ requests final.core d ↔ o ∈ requests emitted.core d := by
  rw [GeneralRebaseMergeRequests264.requests_merge emitted direct child d o]
  constructor
  · rintro (old|⟨_,fromChild⟩|⟨toChild,_⟩)
    · exact old
    · exact False.elim (child_new (old_request_identity _ _ fromChild).2)
    · exact False.elim (away (identity_before toChild))
  · exact Or.inl

theorem models (m : Assignment) : Models final m ↔ Models emitted m := by
  refine ⟨GeneralNominalVersionedAdministrative232.merge_restrict,?_⟩
  intro valid
  apply merge_models.mpr
  refine ⟨valid,?_,?_,?_⟩
  · rw [no_added_atoms]
    exact PresenceNormalForm.all_nil _ _
  · intro _ absence; cases absence
  · intro e listed
    change e ∈ [GeneralLatePeerRouteInstall311.effect,GeneralLatePeerDirectInstall311.effect,
      GeneralLatePeerFirst311.effect] at listed
    have away : e.plan.packet.site.occurrence.identity ≠ child.occurrence.identity := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at listed
      rcases listed with rfl|rfl|rfl
      · exact Ne.symm child_branch
      · exact Ne.symm child_new
      · exact Ne.symm child_root
    exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun o => (request_eq e.plan.packet.site.occurrence away o).symm)).mp (valid.2.2 e listed).2

end Yulang.GeneralLatePeerMerge311
