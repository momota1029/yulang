import Yulang.GeneralDictionarySupportChoices
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Local semantic transport through actual associated-output merging.
Independent existential witnesses for two Joint predicates are NOT identified.
The same pre-merge model must satisfy both old alias classes and output equations.
No target, transition, or dictionary judgment is changed.

Hypothesis guide:
* output target membership prevents a merge from introducing fresh source names;
  this is needed for transport of Prepared freshness/linkedness.
* packet-key agreement is checked across both OLD alias classes.
* the single model must support every OLD class branch and the added equations.
* SameInputs + a common AssociatedMeaning + both DictionaryOutputs can supply
  those equations, but arbitrary recursive Evidence is not claimed to supply
  either output facet or a common interpretation.
* the operational wrapper additionally consumes the unchanged support-step guards.
No unconditional general V5 residual or independently chosen witness amalgamation
is discharged by this module. -/
namespace Yulang.GeneralDictionaryJointMerge
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalJointCandidates GeneralNominalRecursiveCandidates
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalDemandMerging (Site)
variable {roles : Roles.RoleDecls}

/-- The complete source dictionary, including ordered recursive children, is
transported exactly when the added associated-output equations hold. -/
theorem evidence_merge_iff (registry : Registry) (state : State roles)
    (first last : Site roles) (model : Assignment) (root : Occurrence roles)
    (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (merge state first last).context model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalDemandMerging.outputAtoms first last) := by
  simpa only [merge,GeneralNominalState.extend,GeneralDictionaryOrdinaryTransport.extend,
    GeneralDictionaryOrdinaryTransport.extendState,List.append_nil] using
    GeneralDictionaryOrdinaryTransport.evidence_extend_iff [] []
      (GeneralNominalDemandMerging.outputAtoms first last) registry state.context model root payload

/-- A common associated interpretation supplies the new equations. This is an
output facet premise, not a claim that arbitrary independent dictionaries agree. -/
theorem evidence_merge_of_outputs (registry : Registry) (state : State roles)
    (first last : Site roles)
    (same : GeneralNominalDemandMerging.SameInputs (Models state) first last)
    (meaning : GeneralNominalDemandMerging.AssociatedMeaning)
    (model : Assignment) (valid : Models state model)
    (left : GeneralNominalDemandMerging.DictionaryOutputs meaning model first)
    (right : GeneralNominalDemandMerging.DictionaryOutputs meaning model last)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (evidence : GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload) :
    Models (merge state first last) model ∧
      GeneralDictionaryRecursiveEvidence.Evidence registry (merge state first last).context model root payload := by
  have outputs := GeneralNominalDemandMerging.dictionary_outputs_preserved _ first last same meaning model valid left right
  exact ⟨(merge_models state first last model).mpr ⟨valid,outputs⟩,
    (evidence_merge_iff registry state first last model root payload).mpr ⟨evidence,outputs⟩⟩

/-- Pure ordinary extension with unchanged source domain preserves a prepared
candidate at a particular model. This separates freshness from model existence. -/
theorem branch_extension (registry : Registry) (state : State roles)
    (atoms : List (PresenceNormalForm.Atom Nat))
    (sameSources : ∀ source, source ∈ GeneralNominalState.sources
      (GeneralNominalState.extend state.context.state [] atoms) ↔
      source ∈ GeneralNominalState.sources state.context.state)
    (root : Occurrence roles) (key : Nat) (model : Assignment)
    (added : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms)
    (given : BranchAt registry state root key model) :
    BranchAt registry {state with context := GeneralDictionaryOrdinaryTransport.extend state.context [] atoms []}
      root key model := by
  obtain ⟨d,visible,checked,identity,role,prepared,bounds,located,branch⟩ := given
  obtain ⟨metadata,linked,fresh,old,found,finished,ready,consistent⟩ := prepared
  have eq := Option.some.inj (located.symm.trans found)
  subst old
  have newbranch := (GeneralDictionaryOrdinaryTransport.branch_extended_iff [] [] atoms
    state.context registry root d checked bounds model).mpr ⟨branch,added⟩
  refine ⟨d,visible,checked,identity,role,?_,bounds,located,newbranch⟩
  refine ⟨metadata,?_,?_,bounds,located,?_,?_,model,newbranch⟩
  · constructor
    · intro i; exact ⟨(sameSources _).mpr (linked.1 i).1,(sameSources _).mpr (linked.1 i).2⟩
    · intro output member; exact (sameSources _).mpr (linked.2 output member)
  · intro origin member collision
    simpa only [GeneralDictionaryOrdinaryTransport.extend,GeneralDictionaryOrdinaryTransport.extendState,
      List.append_nil] using fresh origin member ((sameSources _).mp collision)
  · simpa only [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
      GeneralDictionaryOrdinaryTransport.finished_report] using finished
  · simpa only [RequestReady,GeneralDictionaryOrdinaryTransport.generated_extended] using ready

/-- Conversely, a prepared branch in an ordinary extension restricts to the
old context when the source domain is unchanged. Its same model supplies the
old consistency witness. -/
theorem branch_extension_back (registry : Registry) (state : State roles)
    (atoms : List (PresenceNormalForm.Atom Nat))
    (sameSources : ∀ source, source ∈ GeneralNominalState.sources
      (GeneralNominalState.extend state.context.state [] atoms) ↔
      source ∈ GeneralNominalState.sources state.context.state)
    (root : Occurrence roles) (key : Nat) (model : Assignment)
    (given : BranchAt registry
      {state with context := GeneralDictionaryOrdinaryTransport.extend state.context [] atoms []}
      root key model) :
    BranchAt registry state root key model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model atoms := by
  obtain ⟨d,visible,checked,identity,role,prepared,bounds,located,branch⟩ := given
  obtain ⟨metadata,linked,fresh,old,found,finished,ready,consistent⟩ := prepared
  have eq := Option.some.inj (located.symm.trans found)
  subst old
  obtain ⟨oldbranch,added⟩ := (GeneralDictionaryOrdinaryTransport.branch_extended_iff [] [] atoms
    state.context registry root d checked bounds model).mp branch
  refine ⟨⟨d,visible,checked,identity,role,?_,bounds,located,oldbranch⟩,added⟩
  refine ⟨metadata,?_,?_,bounds,located,?_,?_,model,oldbranch⟩
  · constructor
    · intro i; exact ⟨(sameSources _).mp (linked.1 i).1,(sameSources _).mp (linked.1 i).2⟩
    · intro output member; exact (sameSources _).mp (linked.2 output member)
  · intro origin member collision
    have result := fresh origin member ((sameSources _).mpr collision)
    simpa only [GeneralDictionaryOrdinaryTransport.extend,GeneralDictionaryOrdinaryTransport.extendState,
      List.append_nil] using result
  · simpa only [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
      GeneralDictionaryOrdinaryTransport.finished_report] using finished
  · simpa only [RequestReady,GeneralDictionaryOrdinaryTransport.generated_extended] using ready

/-- Real output equations add no fresh source when both demand output targets
already belong to the current source domain. -/
theorem merge_sources (state : State roles) (first last : Site roles)
    (left : ∀ output ∈ first.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (right : ∀ output ∈ last.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state) (source : Nat) :
    source ∈ GeneralNominalState.sources (merge state first last).context.state ↔
      source ∈ GeneralNominalState.sources state.context.state := by
  have added : ∀ atom ∈ GeneralNominalDemandMerging.outputAtoms first last,
      ∀ source ∈ GeneralNominalState.atomSources atom,
      source ∈ GeneralNominalState.sources state.context.state := by
    intro atom present source member
    obtain ⟨a,ha,present⟩ := List.mem_flatMap.mp present
    obtain ⟨b,hb,present⟩ := List.mem_flatMap.mp present
    by_cases names : a.name = b.name
    · simp only [names,ite_true] at present
      simp only [GeneralNominalAllocation.equations,List.mem_cons,List.not_mem_nil] at present
      rcases present with rfl | rfl | impossible
      · simp only [GeneralNominalState.atomSources,GeneralNominalState.typeSources,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact left a ha
        · exact right b hb
      · simp only [GeneralNominalState.atomSources,GeneralNominalState.typeSources,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · exact right b hb
        · exact left a ha
      · cases impossible
    · simp [names] at present
  simp only [merge,GeneralNominalState.extend,GeneralNominalState.sources,List.append_nil,
    List.flatMap_append,List.mem_append]
  constructor
  · rintro (old | original | new)
    · exact Or.inl old
    · exact Or.inr original
    · obtain ⟨atom,ha,hs⟩ := List.mem_flatMap.mp new
      simpa only [GeneralNominalState.sources,List.mem_append] using added atom ha source hs
  · rintro (old | original)
    · exact Or.inl old
    · exact Or.inr (Or.inl original)

/-- Prepared branches survive actual merge, at the SAME model, with every
associated output equation explicit. No independent witnesses are combined. -/
theorem branch_merge (registry : Registry) (state : State roles) (first last : Site roles)
    (left : ∀ output ∈ first.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (right : ∀ output ∈ last.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (root : Occurrence roles) (key : Nat) (model : Assignment)
    (outputs : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last))
    (branch : BranchAt registry state root key model) :
    BranchAt registry (merge state first last) root key model := by
  have transported := branch_extension registry state (GeneralNominalDemandMerging.outputAtoms first last)
    (merge_sources state first last left right) root key model outputs branch
  have context_eq : (merge state first last).context =
      GeneralDictionaryOrdinaryTransport.extend state.context []
        (GeneralNominalDemandMerging.outputAtoms first last) [] := by
    simp [merge,GeneralNominalState.extend,GeneralDictionaryOrdinaryTransport.extend,
      GeneralDictionaryOrdinaryTransport.extendState]
  unfold BranchAt
  rw [context_eq]
  exact transported

/-- Exact branch reduction for actual merge with already-linked output targets. -/
theorem branch_merge_iff (registry : Registry) (state : State roles) (first last : Site roles)
    (left : ∀ output ∈ first.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (right : ∀ output ∈ last.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (root : Occurrence roles) (key : Nat) (model : Assignment) :
    BranchAt registry (merge state first last) root key model ↔
      BranchAt registry state root key model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalDemandMerging.outputAtoms first last) := by
  constructor
  · intro branch
    have context_eq : (merge state first last).context =
        GeneralDictionaryOrdinaryTransport.extend state.context []
          (GeneralNominalDemandMerging.outputAtoms first last) [] := by
      simp [merge,GeneralNominalState.extend,GeneralDictionaryOrdinaryTransport.extend,
        GeneralDictionaryOrdinaryTransport.extendState]
    unfold BranchAt at branch
    rw [context_eq] at branch
    exact branch_extension_back registry state (GeneralNominalDemandMerging.outputAtoms first last)
      (merge_sources state first last left right) root key model branch
  · rintro ⟨branch,outputs⟩
    exact branch_merge registry state first last left right root key model outputs branch

/-- The new representative sees exactly the union of the two old alias classes. -/
theorem alias_merge_first_iff (state : State roles) (first last : Site roles) (identity : Nat) :
    Alias (merge state first last) first.occurrence.identity identity ↔
      Alias state first.occurrence.identity identity ∨
      Alias state last.occurrence.identity identity := by
  constructor
  · intro linked
    rcases GeneralDictionarySupportChoices.alias_merge_cases state first last _ _ linked with
      old | ⟨_,right⟩ | ⟨_,right⟩
    · exact Or.inl old
    · exact Or.inr right
    · exact Or.inl right
  · have lift : ∀ a b, Alias state a b → Alias (merge state first last) a b := by
      intro a b linked
      induction linked with
      | refl => exact .refl _
      | edge member => exact .edge (List.mem_cons_of_mem _ member)
      | symm _ ih => exact ih.symm
      | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    intro linked
    rcases linked with left | right
    · exact lift _ _ left
    · exact (Alias.edge (List.mem_cons_self)).trans (lift _ _ right)

/-- A common pre-merge model for both old alias classes suffices for Joint after
the REAL output merge. The class-key and model-compatibility obligations remain
explicit: separate existential Joint witnesses do not satisfy these premises. -/
theorem joint_merge_shared (registry : Registry) (state : State roles) (first last : Site roles)
    (leftTargets : ∀ output ∈ first.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (rightTargets : ∀ output ∈ last.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (key : Nat)
    (keys : ∀ packet ∈ state.packets,
      (Alias state first.occurrence.identity packet.site.occurrence.identity ∨
       Alias state last.occurrence.identity packet.site.occurrence.identity) →
      packet.declaration.id = key)
    (model : Assignment) (valid : Models state model)
    (outputs : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last))
    (rootBranch : BranchAt registry state first.occurrence key model)
    (classBranches : ∀ site ∈ state.sites,
      (Alias state first.occurrence.identity site.occurrence.identity ∨
       Alias state last.occurrence.identity site.occurrence.identity) →
      BranchAt registry state site.occurrence key model) :
    Joint registry (merge state first last) first.occurrence key := by
  refine ⟨?_, model, (merge_models state first last model).mpr ⟨valid,outputs⟩, ?_, ?_⟩
  · intro packet member linked
    exact keys packet member ((alias_merge_first_iff state first last _).mp linked)
  · exact branch_merge registry state first last leftTargets rightTargets _ key model outputs rootBranch
  · intro site related
    exact branch_merge registry state first last leftTargets rightTargets _ key model outputs
      (classBranches site related.1 ((alias_merge_first_iff state first last _).mp related.2))

/-- Exact semantic residual for Joint at the actual merged representative.
All conditions on the right concern the PRE-merge state, plus the explicit
equations that merge adds. In particular the witness is ONE common model, not
a conjunction of independently inhabited survivor predicates. -/
theorem joint_merge_iff (registry : Registry) (state : State roles) (first last : Site roles)
    (leftTargets : ∀ output ∈ first.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (rightTargets : ∀ output ∈ last.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (key : Nat) :
    Joint registry (merge state first last) first.occurrence key ↔
      (∀ packet ∈ state.packets,
        (Alias state first.occurrence.identity packet.site.occurrence.identity ∨
         Alias state last.occurrence.identity packet.site.occurrence.identity) →
        packet.declaration.id = key) ∧
      ∃ model, Models state model ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model
          (GeneralNominalDemandMerging.outputAtoms first last) ∧
        BranchAt registry state first.occurrence key model ∧
        ∀ site ∈ state.sites,
          (Alias state first.occurrence.identity site.occurrence.identity ∨
           Alias state last.occurrence.identity site.occurrence.identity) →
          BranchAt registry state site.occurrence key model := by
  constructor
  · rintro ⟨keys,model,valid,rootBranch,classBranches⟩
    obtain ⟨oldValid,outputs⟩ := (merge_models state first last model).mp valid
    refine ⟨?_,model,oldValid,outputs,?_,?_⟩
    · intro packet member linked
      exact keys packet member ((alias_merge_first_iff state first last _).mpr linked)
    · exact ((branch_merge_iff registry state first last leftTargets rightTargets _ key model).mp rootBranch).1
    · intro site member linked
      exact ((branch_merge_iff registry state first last leftTargets rightTargets _ key model).mp
        (classBranches site ⟨member,(alias_merge_first_iff state first last _).mpr linked⟩)).1
  · rintro ⟨keys,model,valid,outputs,rootBranch,classBranches⟩
    exact joint_merge_shared registry state first last leftTargets rightTargets key keys model valid
      outputs rootBranch classBranches

/-- Associated dictionary output facets discharge the equation obligation of
`joint_merge_shared`; neither a new target nor a post-state Joint is assumed. -/
theorem joint_merge_of_outputs (registry : Registry) (state : State roles) (first last : Site roles)
    (leftTargets : ∀ output ∈ first.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (rightTargets : ∀ output ∈ last.occurrence.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state)
    (key : Nat)
    (keys : ∀ packet ∈ state.packets,
      (Alias state first.occurrence.identity packet.site.occurrence.identity ∨
       Alias state last.occurrence.identity packet.site.occurrence.identity) →
      packet.declaration.id = key)
    (same : GeneralNominalDemandMerging.SameInputs (Models state) first last)
    (meaning : GeneralNominalDemandMerging.AssociatedMeaning)
    (model : Assignment) (valid : Models state model)
    (left : GeneralNominalDemandMerging.DictionaryOutputs meaning model first)
    (right : GeneralNominalDemandMerging.DictionaryOutputs meaning model last)
    (rootBranch : BranchAt registry state first.occurrence key model)
    (classBranches : ∀ site ∈ state.sites,
      (Alias state first.occurrence.identity site.occurrence.identity ∨
       Alias state last.occurrence.identity site.occurrence.identity) →
      BranchAt registry state site.occurrence key model) :
    Joint registry (merge state first last) first.occurrence key := by
  exact joint_merge_shared registry state first last leftTargets rightTargets key keys model valid
    (GeneralNominalDemandMerging.dictionary_outputs_preserved _ first last same meaning model valid left right)
    rootBranch classBranches

/-- The target-domain side condition is already contained in a prepared branch. -/
theorem branch_output_targets (registry : Registry) (state : State roles)
    (root : Occurrence roles) (key : Nat) (model : Assignment)
    (branch : BranchAt registry state root key model) :
    ∀ output ∈ root.demand.outputs,
      output.target ∈ GeneralNominalState.sources state.context.state := by
  obtain ⟨d,visible,checked,identity,role,prepared,rest⟩ := branch
  exact prepared.2.1.2

/-- For a registered merge partner, Prepared branches themselves establish
the target-domain side conditions of the general shared-model theorem. -/
theorem joint_merge_registered (registry : Registry) (state : State roles)
    (first last : Site roles) (registeredLast : last ∈ state.sites) (key : Nat)
    (keys : ∀ packet ∈ state.packets,
      (Alias state first.occurrence.identity packet.site.occurrence.identity ∨
       Alias state last.occurrence.identity packet.site.occurrence.identity) →
      packet.declaration.id = key)
    (model : Assignment) (valid : Models state model)
    (outputs : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last))
    (rootBranch : BranchAt registry state first.occurrence key model)
    (classBranches : ∀ site ∈ state.sites,
      (Alias state first.occurrence.identity site.occurrence.identity ∨
       Alias state last.occurrence.identity site.occurrence.identity) →
      BranchAt registry state site.occurrence key model) :
    Joint registry (merge state first last) first.occurrence key := by
  exact joint_merge_shared registry state first last
    (branch_output_targets registry state first.occurrence key model rootBranch)
    (branch_output_targets registry state last.occurrence key model
      (classBranches last registeredLast (Or.inr (.refl _))))
    key keys model valid outputs rootBranch classBranches

/-- Conditional operational specialization: given an actually enabled support
merge from a source-formed state, its tracked result is source-formed and Joint.
Registration, generation, novelty and MergeGuard are consumed to construct the
real Step. Target-domain conditions follow from the root branch and registered
last-class branch; the semantic common-model residual stays independent.
This theorem does NOT assert that any such enabled merge exists. -/
theorem sourceformed_merge_joint (registry : Registry)
    (before : GeneralNominalSupport.Tracked roles) (root : Occurrence roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root before)
    (first last : Site roles) (support : List (Occurrence roles))
    (generated : Generated before.current root first.occurrence)
    (registeredFirst : first ∈ before.current.sites)
    (registeredLast : last ∈ before.current.sites)
    (same : GeneralNominalFeedbackSites.SameInputs before.current first last)
    (novel : ¬ Alias before.current first.occurrence.identity last.occurrence.identity)
    (guard : GeneralNominalSupportChoices.MergeGuard before first last support)
    (key : Nat)
    (keys : ∀ packet ∈ before.current.packets,
      (Alias before.current first.occurrence.identity packet.site.occurrence.identity ∨
       Alias before.current last.occurrence.identity packet.site.occurrence.identity) →
      packet.declaration.id = key)
    (model : Assignment) (valid : Models before.current model)
    (outputs : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last))
    (rootBranch : BranchAt registry before.current first.occurrence key model)
    (classBranches : ∀ site ∈ before.current.sites,
      (Alias before.current first.occurrence.identity site.occurrence.identity ∨
       Alias before.current last.occurrence.identity site.occurrence.identity) →
      BranchAt registry before.current site.occurrence key model) :
    GeneralNominalSupportSteps.Step registry root before
      (GeneralNominalSupportSteps.merge before first last support) ∧
    GeneralNominalSupportSteps.SourceFormed registry root
      (GeneralNominalSupportSteps.merge before first last support) ∧
    Joint registry (GeneralNominalSupportSteps.merge before first last support).current
      first.occurrence key := by
  have step : GeneralNominalSupportSteps.Step registry root before
      (GeneralNominalSupportSteps.merge before first last support) :=
    ⟨first.occurrence,generated,.merge first last support registeredFirst registeredLast same novel guard⟩
  exact ⟨step,.update formed step,
    joint_merge_registered registry before.current first last registeredLast key keys model valid
      outputs rootBranch classBranches⟩

end Yulang.GeneralDictionaryJointMerge
