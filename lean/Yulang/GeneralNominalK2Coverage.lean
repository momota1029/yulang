import Yulang.GeneralNominalCandidates

/-! Visible structural cycles do not wait for unrelated unknown descendants.
Alias recurrence retains the earlier completeness certificate. Mixed explicit
nominal-argument cycles are recorded separately, pending an owner decision;
interval bounds are not treated as actual argument edges. -/
namespace Yulang.GeneralNominalK2Coverage

open GeneralNominalState (State)

def AtK2 (state : State) (slot : Fin state.base.slots) : Prop :=
  GeneralSourceK2.Cycle state.view slot ∨ GeneralNominalState.AtK2 state slot

def RootK2 (state : State) (demand : GeneralSourceState.Demand roles) : Prop :=
  GeneralNominalState.Linked state demand ∧ ¬ GeneralNominalState.RootPending state demand ∧
    ∃ index slot, state.base.source slot = (demand.arguments index).1 ∧ AtK2 state slot

theorem old_atK2 (state : State) (slot : Fin state.base.slots)
    (old : GeneralNominalState.AtK2 state slot) : AtK2 state slot := Or.inr old

theorem old_rootK2 (state : State) (demand : GeneralSourceState.Demand roles)
    (old : GeneralNominalState.RootK2 state demand) : RootK2 state demand := by
  obtain ⟨linked,ready,index,slot,equal,cycle⟩ := old
  exact ⟨linked,ready,index,slot,equal,Or.inr cycle⟩

theorem atK2_recurrence (state : State) (slot : Fin state.base.slots)
    (cycle : AtK2 state slot) : GeneralSourceK2.RecursAt state.view slot := by
  rcases cycle with direct | old
  · exact Or.inl direct
  · exact GeneralNominalState.atK2_recurrence state slot old

theorem pending_excludes_K2 (state : State) (demand : GeneralSourceState.Demand roles)
    (pending : GeneralNominalState.RootPending state demand) : ¬ RootK2 state demand :=
  fun rejected => rejected.2.1 pending

theorem direct_cycle_rejects (state : State) (demand : GeneralSourceState.Demand roles)
    (linked : GeneralNominalState.Linked state demand)
    (ready : ¬ GeneralNominalState.RootPending state demand)
    (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots)
    (source : state.base.source slot = (demand.arguments index).1)
    (cycle : GeneralSourceK2.Cycle state.view slot) : RootK2 state demand :=
  ⟨linked,ready,index,slot,source,Or.inl cycle⟩

theorem direct_cycle_with_unresolved_descendant (state : State)
    (root child : Fin state.base.slots) (cycle : GeneralSourceK2.Cycle state.view root)
    (path : GeneralSourceK2.Path state.view root child)
    (unknown : state.view.graph child = .unresolved) :
    AtK2 state root ∧ ¬ GeneralSourceK2.Complete state.view root :=
  ⟨Or.inl cycle, GeneralSourceK2.incomplete_defers state.view root child path unknown⟩

/-- These edges are only explicit, already point-valued parameters. General
non-point endpoints are bounds and cannot certify an actual recursive edge. -/
def ExplicitCycle (state : State) (root : Fin state.base.slots) : Prop :=
  ∃ child, child ∈ GeneralNominalInspection.explicitSuccessors state root ∧
    FiniteWorklist.Path (GeneralNominalInspection.explicitSuccessors state) child root

def MixedUnknown (state : State) (root : Fin state.base.slots) : Prop :=
  ExplicitCycle state root ∧ ¬ AtK2 state root

theorem mixed_unknown_not_K2 (state : State) (root : Fin state.base.slots)
    (unknown : MixedUnknown state root) : ¬ AtK2 state root := unknown.2

theorem nominal_not_atK2 (state : State) (root : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals root = some descriptor) : ¬ AtK2 state root := by
  have hidden :=  state.bodies_opaque root descriptor recorded
  rintro (⟨_,⟨kind,children,head,_⟩,_⟩ | ⟨complete,_⟩)
  · rw [hidden] at head
    cases head
  · apply complete root (.nil root)
    simp [GeneralNormalizedObservation.Snapshot.graph,hidden,GeneralNormalizedObservation.Head.node]

private theorem reachable (state : State) (first last : Fin state.base.slots) :
    last ∈ FiniteWorklist.reachable (GeneralNominalInspection.explicitSuccessors state) state.base.slots first ↔
      FiniteWorklist.Path (GeneralNominalInspection.explicitSuccessors state) first last :=
  FiniteWorklist.reachable_exact _ _ (List.finRange state.base.slots)
    (fun slot => List.mem_finRange slot) (by simp) first last

theorem nominal_cycle_not_supported (state : State) (root : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals root = some descriptor) (cycle : ExplicitCycle state root) :
    ¬ GeneralNominalInspection.NominalSupported state root := by
  intro supported
  obtain ⟨child,edge,path⟩ := cycle
  have rootSeen := (reachable state root root).mpr (.nil root)
  have nominal : (state.nominals root).isSome = true := by simp [recorded]
  exact (supported root rootSeen).2 nominal child edge ((reachable state child root).mpr path)

theorem nominal_cycle_defers (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending context.state root.demand)
    (declaration : GeneralDeclarations.Declaration) (visible : declaration ∈ registry.declarations)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (sameRole : declaration.role = root.demand.role)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : GeneralNominalCandidates.arguments context root = some bounds)
    (visited : GeneralNominalInspection.Bounds context.state)
    (member : visited ∈ (GeneralNominalCandidates.report context declaration bounds).inspected)
    (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals visited.1 = some descriptor)
    (cycle : ExplicitCycle context.state visited.1) :
    GeneralNominalCandidates.InspectionPending registry context root := by
  apply GeneralNominalCandidates.coverage_defers registry context root ready declaration visible checked sameRole bounds located
  intro covered
  rcases covered visited member with nominal | complete
  · obtain ⟨_,_,supported⟩ := nominal
    exact nominal_cycle_not_supported context.state visited.1 descriptor recorded cycle supported
  · apply complete visited.1 (.nil _)
    have hidden :=  context.state.bodies_opaque visited.1 descriptor recorded
    simp [GeneralNormalizedObservation.Snapshot.graph,hidden,GeneralNormalizedObservation.Head.node]

theorem atK2_exact_closed (state : State)
    (closed : ∀ slot, state.view.graph slot ≠ .unresolved) (root : Fin state.base.slots) :
    AtK2 state root ↔ GeneralSourceK2.RecursAt state.view root := by
  constructor
  · exact atK2_recurrence state root
  · intro recurrence
    exact Or.inr ⟨fun slot _ => closed slot, (GeneralSourceK2.graphK2_exact state.view closed root).mpr recurrence⟩

/-- Candidate K2 requires the same applicability/interval facts as before,
but a direct visible cycle is sufficient at an inspected constructor. The
candidate's other blockers remain losslessly visible to inspection pending. -/
def CandidateK2 (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state root.demand ∧
    GeneralNominalCandidates.Metadata registry context ∧
    GeneralNominalState.Linked context.state root.demand ∧
    ∃ declaration ∈ registry.declarations,
      ∃ _checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration,
        declaration.role = root.demand.role ∧
        ∃ bounds, GeneralNominalCandidates.arguments context root = some bounds ∧
          GeneralNominalInspection.Finished (GeneralNominalCandidates.report context declaration bounds) ∧
          GeneralNominalCandidates.Consistent registry context root declaration bounds ∧
          ∃ visited ∈ (GeneralNominalCandidates.report context declaration bounds).inspected,
            AtK2 context.state visited.1

theorem old_candidateK2 (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (old : GeneralNominalCandidates.CandidateK2 registry context root) : CandidateK2 registry context root := by
  obtain ⟨ready,metadata,linked,declaration,visible,checked,role,
    ⟨bounds,located,finished,_,consistent⟩,other,found,visited,member,cycle⟩ := old
  have same := Option.some.inj (located.symm.trans found)
  subst other
  exact ⟨ready,metadata,linked,declaration,visible,checked,role,bounds,located,finished,
    consistent,visited,member,Or.inr cycle⟩

theorem candidate_recurrence (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (cycle : CandidateK2 registry context root) :
    ∃ declaration ∈ registry.declarations, ∃ bounds,
      GeneralNominalCandidates.arguments context root = some bounds ∧
      ∃ visited ∈ (GeneralNominalCandidates.report context declaration bounds).inspected,
        GeneralSourceK2.RecursAt context.state.view visited.1 := by
  obtain ⟨_,_,_,declaration,visible,_,_,bounds,located,_,_,visited,member,cycle⟩ := cycle
  exact ⟨declaration,visible,bounds,located,visited,member,atK2_recurrence _ _ cycle⟩

theorem pending_excludes_candidateK2 (registry : GeneralDeclarations.Registry)
    (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles)
    (pending : GeneralNominalState.RootPending context.state root.demand) :
    ¬ CandidateK2 registry context root := fun cycle => cycle.1 pending

end Yulang.GeneralNominalK2Coverage
