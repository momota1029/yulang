import Yulang.GeneralDictionaryGroundCopy218SaturatedParent
import Yulang.GeneralDictionaryGroundCopy218Refutation

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model childSite model_forms low_high install_step)
open GeneralDictionaryGroundCopy218Reobserve (reobserved reobserve_step)
open GeneralDictionaryGroundCopy218Reinstall (reinstalled newChild newPacket reinstall_step reinstalled_reachable choice_compatible)
open GeneralDictionaryGroundCopy218SaturatedState
open GeneralDictionaryGroundCopy218Refutation (child_eq)
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalSaturationState (Generated)
open GeneralDictionaryGroundCopy218Stability (Supported)

def Good (atoms : List (PresenceNormalForm.Atom Nat)) : Prop :=
  PresenceNormalForm.All CommonNominalFullCarrier.model model atoms ∧ Supported atoms

theorem initial_good : Good initialAtoms := ⟨atoms_initial,supported_initial⟩

theorem selected {atoms} (good : Good atoms) :
    GeneralDictionaryDefaultBoundary208.Local sourceRegistry (stage atoms) childSite.occurrence (.selected 1 []) := by
  have valid := model_if_atoms atoms good.1
  have unique := GeneralDictionaryGroundCopy218Leaf.unique allocation reservation atoms model
    valid.1 low_high (missing good.2)
    (fresh good.2)
  have prepared := GeneralDictionaryGroundCopy218Leaf.prepared allocation reservation atoms model
    valid.1 low_high (missing good.2)
    (fresh good.2)
  have acyclic := GeneralDictionaryGroundCopy218Cycles.acyclic valid model_forms
  have safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepLocal.diagnosticBoundary roles)
      registry (stage atoms) childSite.occurrence := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [child_eq]
      exact GeneralDictionaryGroundCopy218Leaf.known allocation reservation atoms
    · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
      · obtain ⟨_,_,_,slot,_,cycle⟩ := old
        exact no_raw_recurs good.1 slot cycle
      · exact acyclic _ cycle
      · exact acyclic _ cycle
    · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
      · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
        exact no_raw_recurs good.1 visited.1 cycle
      · exact acyclic _ cycle
    · rintro (⟨_,d,visible,role,_,unprepared⟩ | unready)
      · cases GeneralDictionaryGroundCopy218Leaf.leaf_only visible role
        exact unprepared (child_eq.symm ▸ prepared)
      · exact unready (administrative_ready atoms)
  apply GeneralDictionaryDefaultBoundary208.local_iff.mpr
  apply GeneralNominalCenteredHeadAllocV7Boundary.local_iff.mpr
  exact .ordinary (merged_clear atoms) (.selected safe (child_eq.symm ▸ unique) (no_output_conflict atoms))

theorem step_stage {atoms after} (good : Good atoms)
    (step : GeneralDictionaryDefaultBoundary208.Step sourceRegistry root (stage atoms) after) :
    ∃ more, Good more ∧ after = stage more := by
  obtain ⟨focus,generated,action⟩ := step
  have focusCases := generated_from_root_only generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := registered generated
      exact False.elim (absent site member same)
    | refresh context certificate identity member unknown known =>
      exact False.elim (no_refresh good.1 certificate unknown known)
    | reobserve revision certificate improved =>
      exact False.elim (no_reobserve revision improved)
    | equate first last one two equal novel =>
      refine ⟨atoms ++ GeneralNominalAllocation.equations first (.var last),⟨?_,?_⟩,rfl⟩
      · exact (PresenceNormalForm.all_append ..).mpr ⟨good.1,
          (GeneralNominalCaptureMerges.equations_exact model first (.var last)).mpr
            (equal model (model_if_atoms atoms good.1))⟩
      · exact supported_equate good.2 one two
  | refresh focus context certificate identity member unknown known =>
    exact False.elim (no_refresh good.1 certificate unknown known)
  | install candidate enabled novel =>
    rcases focusCases with rootEq | oldEq | newEq
    · exact False.elim (novel (GeneralDictionaryGroundCopy218SaturatedParent.committed candidate rootEq enabled))
    · exact False.elim (no_install_old candidate oldEq enabled)
    · exact False.elim (no_install_new candidate newEq enabled)
  | merge first last one two same novel => exact False.elim (novel (merges_closed one two same))

theorem trace_stage {last}
    (path : B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) reinstalled last) :
    ∃ atoms, Good atoms ∧ last = stage atoms := by
  induction path with
  | refl => exact ⟨initialAtoms,initial_good,rfl⟩
  | tail path step ih =>
    obtain ⟨atoms,good,rfl⟩ := ih
    exact step_stage good step

noncomputable def final : State roles :=
  GeneralDictionaryDefaultExecutor208.terminalState sourceRegistry reinstalled root

theorem final_exit :
    B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) reinstalled final ∧
    ∀ after, ¬ GeneralDictionaryDefaultBoundary208.Step sourceRegistry root final after :=
  GeneralDictionaryDefaultExecutor208.terminal_exit
    (GeneralDictionaryDefaultExecutor208.progress sourceRegistry ⟨rfl,source_checked⟩ reinstalled root reinstalled_reachable)

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

theorem final_stable :
    GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final root ∧
    ∀ focus, Generated final.core.erased.current root focus →
      GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final focus :=
  GeneralDictionaryDefaultKernel208.closure final_exit.2

theorem final_generated :
    Generated final.core.erased.current root childSite.occurrence ∧
    Generated final.core.erased.current root newChild.occurrence ∧
    ∀ focus, Generated final.core.erased.current root focus →
      focus = root ∨ focus = childSite.occurrence ∨ focus = newChild.occurrence := by
  obtain ⟨atoms,good,equal⟩ := final_shape
  rw [equal]
  exact ⟨old_generated atoms,new_generated atoms,fun _ => generated_from_root_only⟩

theorem final_reachable :
    B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root final :=
  B4TargetV5.reachable_steps _ reinstalled_reachable final_exit.1

theorem execution :
    B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) start final := by
  have first : B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) start reinstalled :=
    .tail (.tail (.tail .refl install_step) reobserve_step) reinstall_step
  have last := final_exit.1
  generalize final = finish at last ⊢
  induction last with
  | refl => exact first
  | tail path step ih => exact .tail ih step

/-- All positive premises, including stability of the entire original root after reinstall. -/
theorem positive_premises :
    (GeneralDictionaryDefaultBoundary208.boundary roles).Checked sourceRegistry ∧
    GeneralNominalSourceFormation.InitialSource sourceRegistry context root ∧
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
    GeneralNominalGroundAccessibility.GroundRoots context root [rootPattern] ∧
    GeneralNominalCenteredHeadWFSource.Coverage sourceRegistry interpretation ∧
    (GeneralDictionaryDefaultBoundary208.boundary roles).Initial sourceRegistry root start ∧
    GeneralNominalCycleSteps.ChoiceCompatible reobserved.core.erased.current newPacket ∧
    GeneralDictionaryDefaultBoundary208.Step sourceRegistry root reobserved reinstalled ∧
    B4Target.Steps (GeneralDictionaryDefaultBoundary208.Step sourceRegistry root) start final ∧
    B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root final ∧
    GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final root ∧
    (∀ focus, Generated final.core.erased.current root focus →
      GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final focus) ∧
    Generated final.core.erased.current root childSite.occurrence ∧
    Generated final.core.erased.current root newChild.occurrence ∧
    (∀ focus, Generated final.core.erased.current root focus →
      focus = root ∨ focus = childSite.occurrence ∨ focus = newChild.occurrence) ∧
    GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final childSite.occurrence ∧
    (∀ child ∈ ([] : List (Occurrence roles)), GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final child) ∧
    GeneralDictionaryDefaultBoundary208.Local sourceRegistry final childSite.occurrence (.selected 1 []) ∧
    Models final model ∧
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => (GeneralDictionaryDefaultBoundary208.boundary roles).Evidence
        sourceRegistry final model child dictionary) [] [] :=
  ⟨⟨rfl,source_checked⟩,source,(fun _ => rfl),ground,coverage,initial_source,choice_compatible,reinstall_step,execution,
    final_reachable,final_stable.1,final_stable.2,final_generated.1,final_generated.2.1,final_generated.2.2,
    final_stable.2 _ final_generated.1,(by intro _ member; cases member),final_selected,final_models,.nil⟩

theorem not_evidenceNode :
    ¬ B4SkeletonV7.EvidenceNode (GeneralDictionaryDefaultBoundary208.boundary roles) := by
  intro node
  exact final_no_evidence (node sourceRegistry ⟨rfl,source_checked⟩ final root final_reachable model final_models
    childSite.occurrence 1 [] [] (Or.inr final_generated.1) (final_stable.2 _ final_generated.1)
    (by intro _ member; cases member) final_selected .nil)

end Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation
