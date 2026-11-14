import Yulang.GeneralNominalCenteredHeadAllocMergeState

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocMergeStable
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralNominalCenteredHeadAllocMergeSource GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadMatStepJournal GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalSaturationState (Alias Generated)

theorem head_holds {data : GeneralNominalState.State} (head : GeneralNominalSupport.Head data identity test observation)
    (valid : observation.Holds assignment) : test.Holds (assignment identity).1 := by
  cases head with
  | scalar => exact valid
  | structural slot kind children recorded =>
      refine ⟨List.ofFn (fun index => (assignment (data.base.source (children index))).1),List.length_ofFn,?_⟩
      have equal := GeneralNominalStructuralReadback.shape_values (data.view.shapes kind) children
        (GeneralNominalCommonBridge.assignment data.base assignment)
      exact equal.symm ▸ valid
  | nominal slot descriptor recorded =>
      obtain ⟨arguments,fit,equal⟩ := valid
      exact ⟨arguments,GeneralNominalLinearMaterializationFacts.fitsAll_length _ _ _ _ fit,equal⟩

theorem no_refresh (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh (stage atoms) nextContext)
    (unknown : ¬ GeneralNominalState.Known (stage atoms).core.erased.current.context.state identity)
    (known : GeneralNominalState.Known nextContext.state identity) : False := by
  have nonzero : identity ≠ 0 := by
    rintro rfl
    exact unknown ⟨(0 : Fin 1),rfl,Or.inl (by intro h; cases h)⟩
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  obtain ⟨facts,trusted,sound⟩ := certificate.cache observation (GeneralNominalSupport.head_recorded head)
  have valid := head_holds head (sound counter (cut facts trusted))
  have bottom : (counter identity).1 = .bottom := by simp [counter,nonzero]
  rw [bottom] at valid
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head test valid

theorem generated_only (given : Generated (stage atoms).core.erased.current root focus) :
    focus = root ∨ focus = aSite.occurrence ∨ focus = bSite.occurrence := by
  induction given with
  | root => exact Or.inl rfl
  | child prior member ih =>
      change (_,_) ∈ [] ++ (children.map fun child => (root,child)) at member
      obtain ⟨child,present,equal⟩ := List.mem_map.mp member
      have same := congrArg Prod.snd equal
      rw [children_exact] at present
      rcases List.mem_cons.mp present with rfl | present
      · exact Or.inr (Or.inl same.symm)
      · cases List.mem_singleton.mp present; exact Or.inr (Or.inr same.symm)
  | alias prior one two same ih =>
      change _ ∈ [GeneralNominalDemandMerging.pointSite root,aSite.observed,bSite.observed] at two
      rcases List.mem_cons.mp two with rfl | two
      · exact Or.inl rfl
      · rcases List.mem_cons.mp two with rfl | two
        · exact Or.inr (Or.inl rfl)
        · cases List.mem_singleton.mp two; exact Or.inr (Or.inr rfl)

theorem registered (given : Generated (stage atoms).core.erased.current root focus) :
    ∃ site ∈ (stage atoms).core.erased.current.sites, site.occurrence = focus := by
  rcases generated_only given with rfl | rfl | rfl
  · exact ⟨_,List.mem_cons_self,rfl⟩
  · exact ⟨_,List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · exact ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),rfl⟩

theorem merges_closed (one : first ∈ (stage atoms).core.sites) (two : last ∈ (stage atoms).core.sites)
    (same : SameInputs models first last) : Alias (stage atoms).core.erased.current first.occurrence.identity last.occurrence.identity := by
  change first ∈ [plan.input,aSite,bSite] at one
  change last ∈ [plan.input,aSite,bSite] at two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
  all_goals first
    | exact .refl _
    | exact .edge (List.mem_singleton_self _)
    | exact .symm (.edge (List.mem_singleton_self _))
    | exact False.elim (by have bad := same.1; cases bad)

def Owned (identity : Nat) : Prop := identity = 0 ∨
  ∃ key : GeneralNominalIdentities.Origin, key.1 = root.identity ∧ GeneralNominalIdentities.source snapshot.seed key = identity
def Supported (atoms : List (PresenceNormalForm.Atom Nat)) : Prop :=
  ∀ identity ∈ atoms.flatMap GeneralNominalState.atomSources, Owned identity

theorem source_owned (supported : Supported atoms)
    (member : identity ∈ GeneralNominalState.sources (stage atoms).core.erased.current.context.state) : Owned identity := by
  simp only [GeneralNominalState.sources,List.mem_append] at member
  rcases member with ((type | row) | reserved) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp type
    change Fin 1 at slot
    change slot.val = identity at equal
    exact Or.inl (equal.symm.trans (congrArg Fin.val (Subsingleton.elim slot (0 : Fin 1))))
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp row
    change Fin 1 at slot
    change slot.val = identity at equal
    exact Or.inl (equal.symm.trans (congrArg Fin.val (Subsingleton.elim slot (0 : Fin 1))))
  · change identity ∈ ([] ++ GeneralNominalAllocation.reserved snapshot registry root.identity) ++ [] at reserved
    simp only [List.nil_append,List.append_nil] at reserved
    obtain ⟨key,member,equal⟩ := List.mem_map.mp reserved
    refine Or.inr ⟨key,?_,equal⟩
    change key ∈ [_,_,_,_] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · exact supported identity ordinary

theorem supported_initial : Supported initialAtoms := by
  intro identity member
  have private_atoms : packet.privateContext.state.ordinary =
      [.tyLe (.var 0) (.var 0),.tyLe (.var 0) (.var 0)] := by
    change (GeneralNominalRecursiveCandidates.privateState registry context root declaration [(0,0)]).ordinary = _
    unfold GeneralNominalRecursiveCandidates.privateState
    rw [report_exact]
    rfl
  have merge_atoms : mergeAtoms = GeneralNominalAllocation.equations aTarget (.var bTarget) := by
    unfold mergeAtoms GeneralNominalDemandMerging.outputAtoms
    simp only [Site.observed,a_outputs,b_outputs]
    rfl
  change identity ∈ (packet.privateContext.state.ordinary ++ mergeAtoms).flatMap GeneralNominalState.atomSources at member
  rw [private_atoms,merge_atoms] at member
  change identity ∈ [0,0,0,0,aTarget,bTarget,bTarget,aTarget] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Or.inl rfl | exact Or.inr ⟨_,rfl,rfl⟩

theorem step_stage (good : Good atoms) (supported : Supported atoms)
    (action : Step registry root (stage atoms) after) :
    ∃ more, Good more ∧ Supported more ∧ after = stage more := by
  obtain ⟨focus,generated,action⟩ := action
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := registered generated
        exact False.elim (absent site member same)
    | refresh nextContext certificate identity member unknown known =>
        exact False.elim (no_refresh certificate unknown known)
    | reobserve revision certificate improved =>
        exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision
          (by intro _ _ impossible; cases impossible) revision improved)
    | equate first last one two equal novel =>
        refine ⟨atoms ++ GeneralNominalAllocation.equations first (.var last),⟨?_,?_⟩,?_,rfl⟩
        · apply (PresenceNormalForm.all_append ..).mpr
          exact ⟨good.1,(GeneralNominalCaptureMerges.equations_exact uniform first (.var last)).mpr
            ⟨subtype_refl _,subtype_refl _⟩⟩
        · exact fun _ member => List.mem_append_left _ (good.2 member)
        · intro identity member
          rw [List.flatMap_append] at member
          rcases List.mem_append.mp member with old | fresh
          · exact supported identity old
          · simp only [GeneralNominalAllocation.equations,GeneralNominalState.atomSources,
              GeneralNominalState.typeSources,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
              List.mem_cons,List.not_mem_nil,or_false] at fresh
            rcases fresh with rfl | rfl | rfl | rfl
            · exact source_owned supported one
            · exact source_owned supported two
            · exact source_owned supported two
            · exact source_owned supported one
  | refresh focus nextContext certificate identity member unknown known =>
      exact False.elim (no_refresh certificate unknown known)
  | install other enabled novel =>
      obtain ⟨assignment,valid,_⟩ := enabled.common
      exact False.elim (empty_models good.2 ⟨assignment,valid⟩)
  | merge first last one two same novel => exact False.elim (novel (merges_closed one two same))

theorem trace_stage (path : B4Target.Steps (Step registry root) merged final) :
    ∃ atoms, Good atoms ∧ Supported atoms ∧ final = stage atoms := by
  induction path with
  | refl => exact ⟨initialAtoms,good_initial,supported_initial,rfl⟩
  | tail path action ih =>
      obtain ⟨atoms,good,supported,rfl⟩ := ih
      exact step_stage good supported action

noncomputable abbrev final := GeneralNominalCenteredHeadMatStepExecutor.terminalState registry merged root
theorem final_exit : GeneralNominalCenteredHeadMatStepExecutor.Exit registry merged root final :=
  GeneralNominalCenteredHeadMatStepExecutor.terminal_exit
    (GeneralNominalCenteredHeadAllocExecutor.progress sourceRegistry ⟨rfl,source_checked⟩ merged root merged_reachable)
theorem final_shape : ∃ atoms, Good atoms ∧ Supported atoms ∧ final = stage atoms := trace_stage final_exit.1
private theorem trace_trans {step : α → α → Prop}
    (one : B4Target.Steps step a b) (two : B4Target.Steps step b c) : B4Target.Steps step a c := by
  induction two with
  | refl => exact one
  | tail _ action ih => exact .tail ih action
theorem final_reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) sourceRegistry root final := by
  obtain ⟨first,initial,path⟩ := merged_reachable
  exact ⟨first,initial,trace_trans path final_exit.1⟩
theorem final_stable : Stable registry final root := (closure final_exit.2).1

end Yulang.GeneralNominalCenteredHeadAllocMergeStable
