import Yulang.GeneralDictionaryEarlyMergeExample
import Yulang.GeneralNominalDownstreamSteps

/-! Same-input merging preserves diagnostic identities. An actual checked
source trace exhibits two equal demands still present after their alias merge.
Thus a bound on semantic classes is not itself a bound on allocated identities.
This does not assert an unbounded or infinite execution. -/
namespace Yulang.GeneralNominalBudgetMergeRetention
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalDownstreamSteps
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (context state model displayRoot)
open GeneralDictionaryEarlyMergeExample

private theorem no_alias_edges {snapshot : State roles} (empty : snapshot.aliases = [])
    {first last : Nat} (same : Alias snapshot first last) : first = last := by
  induction same with
  | refl => rfl
  | edge member => rw [empty] at member; cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem distinct_children : (child 10).identity ≠ (child 11).identity := by
  intro equal
  have same := (GeneralNominalIdentities.source_identity (state true).seed _ _).mp equal
  have impossible := congrArg (fun x : GeneralNominalIdentities.Origin => x.2.2.2.1) same
  contradiction

theorem installation : Step registry displayRoot (start displayRoot) before :=
  ⟨displayRoot,.root,.install packet [] enabled novel
    (GeneralNominalDownstreamSupport.source_packet _ _ packet_guard)⟩

theorem before_formed : SourceFormed registry displayRoot before :=
  .update (.initial _ source) installation

theorem merge_step : Step registry displayRoot before finish := by
  have generated : Generated before.current displayRoot (child 10) := by
    apply Generated.child .root
    change (displayRoot,child 10) ∈ [] ++ packet.children.map _
    change (displayRoot,child 10) ∈ [] ++ children.map _
    rw [children_exact]
    simp [GeneralNominalDemandMerging.pointSite]
  refine ⟨child 10,generated,.merge (site 10) (site 11) _ (site_present 10 (Or.inl rfl))
    (site_present 11 (Or.inr rfl)) inputs_same ?_ ?_⟩
  · exact fun same => distinct_children (no_alias_edges rfl same)
  · exact GeneralDictionarySupportEvidence.merge_guard_of_exact before
      (GeneralNominalDownstreamSteps.formed_exact before_formed) _ _ inputs_same

theorem finish_formed : SourceFormed registry displayRoot finish := .update before_formed merge_step

theorem identities_retained : finish.current.sites = before.current.sites ∧
    finish.current.edges = before.current.edges ∧ finish.current.packets = before.current.packets := ⟨rfl,rfl,rfl⟩

theorem duplicate_occurrences_remain :
    (child 10).demand = (child 11).demand ∧
    (child 10).identity ≠ (child 11).identity ∧
    site 10 ∈ finish.current.sites ∧ site 11 ∈ finish.current.sites ∧
    Alias finish.current (child 10).identity (child 11).identity :=
  ⟨rfl,distinct_children,site_present 10 (Or.inl rfl),site_present 11 (Or.inr rfl),
    .edge (by exact List.mem_cons_self)⟩

/-- Even equality of the entire demand, not merely the unnamed inputs, does
not collapse occurrence IDs in the lossless state. -/
theorem not_literal_demand_injective :
    ¬ (∀ first ∈ finish.current.sites, ∀ last ∈ finish.current.sites,
      first.occurrence.demand = last.occurrence.demand → first.occurrence.identity = last.occurrence.identity) := by
  intro injective
  exact distinct_children (injective (site 10) duplicate_occurrences_remain.2.2.1
    (site 11) duplicate_occurrences_remain.2.2.2.1 rfl)

theorem actual_merged_duplicates :
    Checked registry ∧ SourceFormed registry displayRoot finish ∧ Models finish.current model ∧
    (child 10).demand = (child 11).demand ∧ (child 10).identity ≠ (child 11).identity ∧
    Alias finish.current (child 10).identity (child 11).identity :=
  ⟨registry_checked,finish_formed,finish_model,duplicate_occurrences_remain.1,distinct_children,
    duplicate_occurrences_remain.2.2.2.2⟩

/-- Output and child allocation uses the occurrence identity, not an alias
representative. Equal requests can therefore allocate distinct child sites. -/
theorem invocation_allocation_distinct (snapshot : GeneralNominalState.State) (reg : Registry)
    (key purpose owner position : Nat) :
    GeneralNominalAllocation.source snapshot reg (child 10).identity
      (GeneralNominalAllocation.origin (child 10).identity key purpose owner position) ≠
    GeneralNominalAllocation.source snapshot reg (child 11).identity
      (GeneralNominalAllocation.origin (child 11).identity key purpose owner position) :=
  GeneralNominalAllocation.distinct_invocations snapshot reg _ _ key purpose owner position distinct_children

end Yulang.GeneralNominalBudgetMergeRetention
