import Yulang.GeneralDictionaryGroundCopy218Stability
import Yulang.GeneralDictionaryGroundCopy218Obstruction
import Yulang.GeneralDictionaryGroundCopy218Leaf
import Yulang.GeneralDictionarySubtreeTermination218

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218Refutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source GeneralDictionaryGroundCopy218Install
open GeneralDictionaryGroundCopy218Reobserve GeneralDictionaryGroundCopy218Obstruction
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalSaturationState (Generated Alias)

theorem child_eq : childSite.occurrence = GeneralDictionaryGroundCopy218Leaf.oldChild := by
  have arguments := funext child_arguments
  change (⟨GeneralDictionaryGroundCopy218Leaf.childId,⟨1,childSite.occurrence.demand.arguments,[],_⟩⟩ : Occurrence roles) = _
  rw [arguments]
  rfl

theorem stage_context (atoms) : (stage atoms).core.erased.current.context =
    GeneralDictionaryGroundCopy218Leaf.ctx installedAllocation installedReservation atoms := rfl

theorem parent_outside (atoms) : ¬ Generated (stage atoms).core.erased.current childSite.occurrence root := by
  intro reached
  have equal := generated_from_child_only reached
  have different := congrArg (fun o : Occurrence roles => o.demand.role) equal
  cases different

theorem registered_child (atoms) :
    ∃ site ∈ (stage atoms).core.erased.current.sites, site.occurrence = childSite.occurrence :=
  ⟨childSite.observed,by rw [raw_sites_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩

theorem administrative_ready (atoms) :
    GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady (stage atoms) childSite.occurrence := by
  refine ⟨⟨childSite,by rw [sites_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩,?_⟩
  intro first one _ last two same
  exact merges_closed one two same

theorem merged_clear (atoms) :
    ¬ GeneralNominalCenteredHeadAllocMergedConflict.MergedOutputConflict (stage atoms) childSite.occurrence := by
  rintro ⟨⟨a,b,member,_⟩,_⟩
  cases member

open GeneralDictionaryGroundCopy218Stability (Supported)

def Good (atoms : List (PresenceNormalForm.Atom Nat)) : Prop :=
  PresenceNormalForm.All CommonNominalFullCarrier.model model atoms ∧ Supported atoms

theorem initial_good : Good initialAtoms := ⟨atoms_initial,GeneralDictionaryGroundCopy218Stability.supported_initial⟩

theorem selected {atoms} (good : Good atoms) :
    GeneralDictionaryDefaultBoundary208.Local sourceRegistry (stage atoms) childSite.occurrence (.selected 1 []) := by
  have valid := model_if_atoms atoms good.1
  have unique := GeneralDictionaryGroundCopy218Leaf.unique installedAllocation installedReservation atoms model
    valid.1 low_high (GeneralDictionaryGroundCopy218Stability.missing good.2)
    (GeneralDictionaryGroundCopy218Stability.fresh good.2)
  have prepared := GeneralDictionaryGroundCopy218Leaf.prepared installedAllocation installedReservation atoms model
    valid.1 low_high (GeneralDictionaryGroundCopy218Stability.missing good.2)
    (GeneralDictionaryGroundCopy218Stability.fresh good.2)
  have acyclic := GeneralDictionaryGroundCopy218Cycles.acyclic valid model_forms
  have safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepLocal.diagnosticBoundary roles)
      registry (stage atoms) childSite.occurrence := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [child_eq]
      exact GeneralDictionaryGroundCopy218Leaf.known installedAllocation installedReservation atoms
    · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
      · obtain ⟨_,_,_,slot,_,cycle⟩ := old
        exact GeneralDictionaryGroundCopy218Stability.no_raw_recurs good.1 slot cycle
      · exact acyclic _ cycle
      · exact acyclic _ cycle
    · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
      · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
        exact GeneralDictionaryGroundCopy218Stability.no_raw_recurs good.1 visited.1 cycle
      · exact acyclic _ cycle
    · rintro (⟨_,d,visible,role,_,unprepared⟩ | unready)
      · cases GeneralDictionaryGroundCopy218Leaf.leaf_only visible role
        exact unprepared (child_eq.symm ▸ prepared)
      · exact unready (administrative_ready atoms)
  apply GeneralDictionaryDefaultBoundary208.local_iff.mpr
  apply GeneralNominalCenteredHeadAllocV7Boundary.local_iff.mpr
  exact .ordinary (merged_clear atoms) (.selected safe (child_eq.symm ▸ unique) (no_output_conflict atoms))

theorem step_stage {atoms after} (good : Good atoms)
    (step : GeneralDictionaryDefaultBoundary208.Step sourceRegistry childSite.occurrence (stage atoms) after) :
    ∃ more, Good more ∧ after = stage more := by
  obtain ⟨focus,generated,action⟩ := step
  have focusEq := generated_from_child_only generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := registered_child atoms
      exact False.elim (absent site member (same.trans focusEq.symm))
    | refresh context certificate identity member unknown known =>
      exact False.elim (GeneralDictionaryGroundCopy218Stability.no_refresh good.1 certificate unknown known)
    | reobserve revision certificate improved =>
      exact False.elim (GeneralDictionaryGroundCopy218Stability.no_reobserve revision improved)
    | equate first last one two equal novel =>
      refine ⟨atoms ++ GeneralNominalAllocation.equations first (.var last),⟨?_,?_⟩,rfl⟩
      · exact (PresenceNormalForm.all_append ..).mpr ⟨good.1,
          (GeneralNominalCaptureMerges.equations_exact model first (.var last)).mpr
            (equal model (model_if_atoms atoms good.1))⟩
      · exact GeneralDictionaryGroundCopy218Stability.supported_equate good.2 one two
  | refresh focus context certificate identity member unknown known =>
    exact False.elim (GeneralDictionaryGroundCopy218Stability.no_refresh good.1 certificate unknown known)
  | install candidate enabled novel => exact False.elim (no_install candidate focusEq enabled)
  | merge first last one two same novel => exact False.elim (novel (merges_closed one two same))

theorem trace_stage {last}
    (path : B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry childSite.occurrence) reobserved last) :
    ∃ atoms, Good atoms ∧ last = stage atoms := by
  induction path with
  | refl => exact ⟨initialAtoms,initial_good,rfl⟩
  | tail path step ih =>
    obtain ⟨atoms,good,rfl⟩ := ih
    exact step_stage good step

noncomputable def final : State roles :=
  GeneralDictionaryDefaultExecutor208.terminalState sourceRegistry reobserved childSite.occurrence

theorem final_exit :
    B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry childSite.occurrence) reobserved final ∧
    B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root final ∧
    Generated final.core.erased.current root childSite.occurrence ∧
    GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final childSite.occurrence :=
  GeneralDictionarySubtreeTermination218.terminal ⟨rfl,source_checked⟩ reobserved_reachable (generated_child initialAtoms)

theorem final_shape : ∃ atoms, Good atoms ∧ final = stage atoms := trace_stage final_exit.1

theorem final_models : Models final model := by
  obtain ⟨atoms,good,equal⟩ := final_shape
  rw [equal]
  exact model_if_atoms atoms good.1

theorem final_selected :
    GeneralDictionaryDefaultBoundary208.Local sourceRegistry final childSite.occurrence (.selected 1 []) := by
  obtain ⟨atoms,good,equal⟩ := final_shape
  rw [equal]
  exact selected good

theorem final_no_evidence :
    ¬ (GeneralDictionaryDefaultBoundary208.boundary roles).Evidence sourceRegistry final model
      childSite.occurrence (.node 1 []) := by
  obtain ⟨atoms,good,equal⟩ := final_shape
  rw [equal]
  exact no_evidence model (model_if_atoms atoms good.1) []

theorem execution :
    B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) start final := by
  have first : B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) start reobserved :=
    .tail (.tail .refl install_step) reobserve_step
  have last := (GeneralDictionarySubtreeTermination218.trace_lift
    (generated_child initialAtoms) final_exit.1).1
  generalize final = finish at last ⊢
  induction last with
  | refl => exact first
  | tail path step ih => exact .tail ih step

/-- The original saturation root is reachable; stability is required at the
selected generated child, exactly as quantified by EvidenceAt. -/
theorem positive_premises :
    (GeneralDictionaryDefaultBoundary208.boundary roles).Checked sourceRegistry ∧
    GeneralNominalSourceFormation.InitialSource sourceRegistry context root ∧
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
    GeneralNominalGroundAccessibility.GroundRoots context root [rootPattern] ∧
    GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry interpretation ∧
    (GeneralDictionaryDefaultBoundary208.boundary roles).Initial sourceRegistry root start ∧
    B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) start final ∧
    B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root final ∧
    Generated final.core.erased.current root childSite.occurrence ∧
    GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final childSite.occurrence ∧
    (∀ child ∈ ([] : List (Occurrence roles)), GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final child) ∧
    GeneralDictionaryDefaultBoundary208.Local sourceRegistry final childSite.occurrence (.selected 1 []) ∧
    Models final model ∧
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => (GeneralDictionaryDefaultBoundary208.boundary roles).Evidence
        sourceRegistry final model child dictionary) [] [] :=
  ⟨⟨rfl,source_checked⟩,source,(fun _ => rfl),ground,coverage,initial_source,execution,
    final_exit.2.1,final_exit.2.2.1,final_exit.2.2.2,
    (by intro _ member; cases member),final_selected,final_models,.nil⟩

theorem not_evidenceNode :
    ¬ B4SkeletonV7.EvidenceNode (GeneralDictionaryDefaultBoundary208.boundary roles) := by
  intro node
  exact final_no_evidence (node sourceRegistry ⟨rfl,source_checked⟩ final root final_exit.2.1 model final_models
    childSite.occurrence 1 [] [] (Or.inr final_exit.2.2.1) final_exit.2.2.2
    (by intro _ member; cases member) final_selected .nil)

end Yulang.GeneralDictionaryGroundCopy218Refutation
