import Yulang.GeneralNominalCenteredHeadAllocMergeInstall

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocMergeState
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralNominalCenteredHeadAllocMergeSource GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalSaturationState (Alias Generated)
open GeneralNominalCenteredHeadMatStepObservations

theorem installed_sites : installed.core.sites = [plan.input,aSite,bSite] := rfl
theorem installed_raw_sites : installed.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,aSite.observed,bSite.observed] := rfl
theorem a_outputs : aSite.occurrence.demand.outputs = [⟨0,aTarget⟩] := rfl
theorem b_outputs : bSite.occurrence.demand.outputs = [⟨0,bTarget⟩] := rfl
theorem a_nonzero : aTarget ≠ 0 := by
  have above := GeneralNominalIdentities.source_above_seed snapshot.seed
    (GeneralNominalAllocation.origin root.identity 37 5 (GeneralNominalIdentities.pair 42 43) 0)
  change 0 < aTarget at above; omega
theorem child_ids_distinct : aSite.occurrence.identity ≠ bSite.occurrence.identity := by
  intro same
  have key := (GeneralNominalIdentities.source_identity snapshot.seed _ _).mp same
  have bad := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) key
  contradiction
theorem a_above_root : root.identity < aSite.occurrence.identity :=
  GeneralNominalIdentities.source_above_invocation snapshot.seed (root.identity,37,6,42,0)
theorem b_above_root : root.identity < bSite.occurrence.identity :=
  GeneralNominalIdentities.source_above_invocation snapshot.seed (root.identity,37,6,44,0)
theorem generated_a : Generated installed.core.erased.current root aSite.occurrence :=
  .child .root (installed_child (by change aSite.occurrence ∈ children; rw [children_exact]; exact List.mem_cons_self))
theorem generated_b : Generated installed.core.erased.current root bSite.occurrence :=
  .child .root (installed_child (by change bSite.occurrence ∈ children; rw [children_exact]; simp))
theorem same_inputs : SameInputs (Models installed) aSite bSite := ⟨rfl,.nil⟩
theorem not_aliased : ¬ Alias installed.core.erased.current aSite.occurrence.identity bSite.occurrence.identity := by
  intro equal
  have identity : ∀ a b, Alias installed.core.erased.current a b → a = b := by
    intro a b related
    induction related with
    | refl => rfl
    | edge member => cases member
    | symm _ ih => exact ih.symm
    | trans _ _ one two => exact one.trans two
  exact child_ids_distinct (identity _ _ equal)

abbrev merged := merge installed aSite bSite
theorem merge_step : GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root installed merged :=
  ⟨aSite.occurrence,generated_a,.merge aSite bSite (by rw [installed_sites]; simp)
    (by rw [installed_sites]; simp) same_inputs not_aliased⟩
theorem merged_reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) sourceRegistry root merged :=
  ⟨start,initial_source,.tail (.tail .refl install_step) merge_step⟩

def stage (atoms : List (PresenceNormalForm.Atom Nat)) : State roles :=
  { merged with core := { merged.core with erased := { merged.core.erased with current :=
    { merged.core.erased.current with context :=
      ⟨{ merged.core.erased.current.context.state with ordinary := atoms },context.interpretation⟩ } } } }

abbrev mergeAtoms := GeneralNominalDemandMerging.outputAtoms aSite.observed bSite.observed
abbrev initialAtoms := merged.core.erased.current.context.state.ordinary
theorem stage_initial : stage initialAtoms = merged := rfl
def Good (atoms : List (PresenceNormalForm.Atom Nat)) : Prop :=
  PresenceNormalForm.All CommonNominalFullCarrier.model uniform atoms ∧ mergeAtoms ⊆ atoms

theorem good_initial : Good initialAtoms := by
  refine ⟨?_,fun _ h => List.mem_append_right _ h⟩
  apply (PresenceNormalForm.all_append ..).mpr
  refine ⟨?_,?_⟩
  · exact (head_model source_uniform).1.2.2
  · apply (GeneralNominalDemandMerging.output_atoms_exact ..).mpr
    intro a one b two _
    change a ∈ aSite.occurrence.demand.outputs at one
    change b ∈ bSite.occurrence.demand.outputs at two
    rw [a_outputs] at one; rw [b_outputs] at two
    cases List.mem_singleton.mp one; cases List.mem_singleton.mp two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem raw_uniform (good : Good atoms) : GeneralNominalState.Models (stage atoms).core.erased.current.context.state uniform :=
  ⟨source_uniform.1,source_uniform.2.1,good.1⟩

theorem empty_models (covered : mergeAtoms ⊆ atoms) : ¬ ∃ assignment, Models (stage atoms) assignment := by
  rintro ⟨assignment,valid⟩
  have branch := valid.2.2.2.2.1 plan (List.mem_singleton_self _)
  have outputs := branch.2.2
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs at outputs
  rw [schema_exact] at outputs
  have a := outputs _ (List.mem_cons_self)
  have b := outputs _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have equal := (GeneralNominalDemandMerging.output_atoms_exact _ _ assignment).mp
    (fun atom member => valid.1.2.2 atom (covered member))
  have same := equal ⟨0,aTarget⟩ (a_outputs.symm ▸ List.mem_singleton_self _)
    ⟨0,bTarget⟩ (b_outputs.symm ▸ List.mem_singleton_self _) rfl
  exact GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_not_variant
    ⟨subtype_trans a.2 (subtype_trans same.1 b.1),subtype_trans b.2 (subtype_trans same.2 a.1)⟩

theorem no_discharged (done : GeneralNominalSupport.Discharged (stage atoms).core.erased.current focus) : False := by
  induction done with
  | packet packet member children ih =>
      cases List.mem_singleton.mp member
      exact ih aSite.occurrence (by change aSite.occurrence ∈ GeneralNominalCenteredHeadAllocMergeSource.children; rw [children_exact]; simp)
  | alias first last one two related prior ih => exact ih

theorem cut : Cut (stage atoms) counter := by
  apply cut_of_recorded source_counter
  · intro site member
    cases List.mem_singleton.mp member
    exact point_root_holds snapshot.seed root (fun _ => rfl) counter
  · intro other member
    cases List.mem_singleton.mp member
    exact inputs source_counter
  · intro other member recorded settled
    exact False.elim (no_discharged (GeneralNominalSettledSupport.packet_settled_demand settled))
  · intro first one last two alias recorded
    have output_bottom (site : Site roles) (member : site ∈ (stage atoms).core.sites)
        (output) (present : output ∈ site.occurrence.demand.outputs) : (counter output.target).1 = .bottom := by
      change site ∈ [plan.input,aSite,bSite] at member
      rcases List.mem_cons.mp member with rfl | member
      · cases present
      · rcases List.mem_cons.mp member with rfl | member
        · rw [a_outputs] at present; cases List.mem_singleton.mp present
          simp [counter,a_nonzero]
        · cases List.mem_singleton.mp member
          rw [b_outputs] at present; cases List.mem_singleton.mp present
          simp [counter,b_nonzero]
    apply (GeneralNominalDemandMerging.output_atoms_exact ..).mpr
    intro a present b found _
    rw [output_bottom first one a present,output_bottom last two b found]
    exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralNominalCenteredHeadAllocMergeState
