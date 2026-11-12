import Yulang.GeneralDictionaryMergeSequence

/-! Simultaneous branch witnesses for finite merge-only folds. The final alias
graph is structural; the RHS uses only pre-fold Models/BranchAt and equations.
This is not a scheduler or a proof that arbitrary merge lists are enabled. -/
namespace Yulang.GeneralDictionaryJointMergeSequence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalJointCandidates
open GeneralNominalDemandMerging (Site outputAtoms)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

/-- All output endpoints are in the original source domain. -/
def Targets (state : State roles) (steps : List (Site roles × Site roles)) : Prop :=
  ∀ pair ∈ steps,
    (∀ output ∈ pair.1.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state) ∧
    (∀ output ∈ pair.2.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)

theorem sources_fold (state : State roles) (steps : List (Site roles × Site roles))
    (targets : Targets state steps) (source : Nat) :
    source ∈ GeneralNominalState.sources
      (steps.foldl (fun current pair => merge current pair.1 pair.2) state).context.state ↔
    source ∈ GeneralNominalState.sources state.context.state := by
  induction steps generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    have ends := targets pair (List.mem_cons_self)
    have one := GeneralDictionaryJointMerge.merge_sources state pair.1 pair.2 ends.1 ends.2
    have remaining : Targets (merge state pair.1 pair.2) rest := by
      intro other member
      have old := targets other (List.mem_cons_of_mem _ member)
      exact ⟨fun o h => (one _).mpr (old.1 o h),fun o h => (one _).mpr (old.2 o h)⟩
    exact (ih _ remaining).trans (one source)

/-- Exact same-model candidate reduction through all accumulated merges. -/
theorem branch_fold (registry : Registry) (state : State roles)
    (steps : List (Site roles × Site roles)) (targets : Targets state steps)
    (root : Occurrence roles) (key : Nat) (model : Assignment) :
    BranchAt registry (steps.foldl (fun current pair => merge current pair.1 pair.2) state)
      root key model ↔ BranchAt registry state root key model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (steps.flatMap (fun pair => outputAtoms pair.1 pair.2)) := by
  induction steps generalizing state with
  | nil => simp
  | cons pair rest ih =>
    have ends := targets pair (List.mem_cons_self)
    have one := GeneralDictionaryJointMerge.merge_sources state pair.1 pair.2 ends.1 ends.2
    have remaining : Targets (merge state pair.1 pair.2) rest := by
      intro other member
      have old := targets other (List.mem_cons_of_mem _ member)
      exact ⟨fun o h => (one _).mpr (old.1 o h),fun o h => (one _).mpr (old.2 o h)⟩
    simp only [List.foldl_cons,List.flatMap_cons,ih _ remaining,
      GeneralDictionaryJointMerge.branch_merge_iff registry state pair.1 pair.2 ends.1 ends.2,
      PresenceNormalForm.all_append]
    exact and_assoc

theorem packets_fold (state : State roles) (steps : List (Site roles × Site roles)) :
    (steps.foldl (fun current pair => merge current pair.1 pair.2) state).packets = state.packets := by
  induction steps generalizing state with
  | nil => rfl
  | cons pair rest ih => simpa only [List.foldl_cons,merge] using ih (merge state pair.1 pair.2)

theorem sites_fold (state : State roles) (steps : List (Site roles × Site roles)) :
    (steps.foldl (fun current pair => merge current pair.1 pair.2) state).sites = state.sites := by
  induction steps generalizing state with
  | nil => rfl
  | cons pair rest ih => simpa only [List.foldl_cons,merge] using ih (merge state pair.1 pair.2)

/-- Final Joint is exactly pre-fold key coherence over the resulting structural
alias graph and ONE pre-fold model satisfying all branch/output obligations. -/
theorem joint_fold (registry : Registry) (state : State roles)
    (steps : List (Site roles × Site roles)) (targets : Targets state steps)
    (root : Occurrence roles) (key : Nat) :
    let after := steps.foldl (fun current pair => merge current pair.1 pair.2) state
    Joint registry after root key ↔
      (∀ packet ∈ state.packets, Alias after root.identity packet.site.occurrence.identity →
        packet.declaration.id = key) ∧
      ∃ model, Models state model ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model
          (steps.flatMap (fun pair => outputAtoms pair.1 pair.2)) ∧
        BranchAt registry state root key model ∧
        ∀ site ∈ state.sites, Alias after root.identity site.occurrence.identity →
          BranchAt registry state site.occurrence key model := by
  dsimp only
  constructor
  · rintro ⟨keys,model,valid,rootBranch,branches⟩
    obtain ⟨old,added⟩ := (GeneralDictionaryMergeSequence.models_fold state steps model).mp valid
    refine ⟨?_,model,old,added,((branch_fold registry state steps targets root key model).mp rootBranch).1,?_⟩
    · simpa only [packets_fold] using keys
    · intro site present alias
      apply ((branch_fold registry state steps targets site.occurrence key model).mp _).1
      apply branches site
      exact ⟨by simpa only [sites_fold] using present,alias⟩
  · rintro ⟨keys,model,valid,added,rootBranch,branches⟩
    refine ⟨?_,model,(GeneralDictionaryMergeSequence.models_fold state steps model).mpr ⟨valid,added⟩,
      (branch_fold registry state steps targets root key model).mpr ⟨rootBranch,added⟩,?_⟩
    · simpa only [packets_fold] using keys
    · intro site related
      apply (branch_fold registry state steps targets site.occurrence key model).mpr
      exact ⟨branches site (by simpa only [sites_fold] using related.1) related.2,added⟩
/-- The fold stores exactly the reversed list of newly joined identity pairs. -/
theorem aliases_fold (state : State roles) (steps : List (Site roles × Site roles)) :
    (steps.foldl (fun current pair => merge current pair.1 pair.2) state).aliases =
      steps.reverse.map (fun pair => (pair.1.occurrence.identity,pair.2.occurrence.identity)) ++
        state.aliases := by
  induction steps generalizing state with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons,ih]
    simp only [merge,List.reverse_cons,List.map_append,List.map_cons,
      List.map_nil,List.append_assoc,List.cons_append,List.nil_append]

/-- Alias is sensitive to graph edges, not their representation order. -/
theorem alias_edges_iff (first last : State roles)
    (same : ∀ pair, pair ∈ first.aliases ↔ pair ∈ last.aliases) (a b : Nat) :
    Alias first a b ↔ Alias last a b := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl _
    | edge member => exact .edge ((same _).mp member)
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro path
    induction path with
    | refl => exact .refl _
    | edge member => exact .edge ((same _).mpr member)
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The actual final alias relation ignores merge-event order/multiplicity. -/
theorem alias_events_iff (state : State roles)
    (first last : List (Site roles × Site roles))
    (same : ∀ pair, pair ∈ first ↔ pair ∈ last) (a b : Nat) :
    Alias (first.foldl (fun current pair => merge current pair.1 pair.2) state) a b ↔
    Alias (last.foldl (fun current pair => merge current pair.1 pair.2) state) a b := by
  apply alias_edges_iff
  intro edge
  simp only [aliases_fold,List.mem_append,List.mem_map,List.mem_reverse]
  simp only [same]

/-- Joint itself is invariant under these merge-only event reorderings, with
linked endpoints explicit. This does not reorder installs or administrative
updates and is not the general V5 canonical-local-order field. -/
theorem joint_events_iff (registry : Registry) (state : State roles)
    (first last : List (Site roles × Site roles))
    (same : ∀ pair, pair ∈ first ↔ pair ∈ last)
    (targets : Targets state first) (root : Occurrence roles) (key : Nat) :
    Joint registry (first.foldl (fun current pair => merge current pair.1 pair.2) state) root key ↔
    Joint registry (last.foldl (fun current pair => merge current pair.1 pair.2) state) root key := by
  have other : Targets state last := fun pair present => targets pair ((same pair).mpr present)
  have one := joint_fold registry state first targets root key
  have two := joint_fold registry state last other root key
  dsimp only at one two
  rw [one,two]
  simp only [alias_events_iff state first last same,
    GeneralDictionaryMergeSequence.event_atoms_iff first last same]

end Yulang.GeneralDictionaryJointMergeSequence
