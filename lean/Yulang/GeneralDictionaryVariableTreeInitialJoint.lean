import Yulang.GeneralDictionaryVariableTreeEvidence

namespace Yulang.GeneralDictionaryVariableTreeInitialJoint
open GeneralDictionaryVariableTreeExample
open GeneralNominalBranchExample (state context root model state_models)
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

theorem root_ready : ¬ GeneralNominalState.RootPending state root.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  exact ⟨0,rfl,Or.inr ⟨GeneralNominalBranchExample.parent,rfl⟩⟩

theorem prepared : Prepared registry context root declaration checked := by
  refine ⟨metadata,initial_source.linked,
    GeneralNominalSourceFormation.initial_fresh context initial_source root.identity,
    [(0,0)],rfl,?_,GeneralDictionaryVariableTree.ready context registry root declaration checked shape,
    model,GeneralDictionaryVariableTree.branch_models context registry root declaration checked shape model state_models⟩
  rw [GeneralNominalTreeFacts.report_exact context declaration tree shape.query]
  exact GeneralNominalTreeFacts.tree_finished state tree none

theorem survivor : Survivor registry context root declaration.id children :=
  ⟨root_ready,declaration,by simp,checked,rfl,rfl,[(0,0)],rfl,prepared,rfl⟩

/-- A concrete first nonterminal Joint comes from the structural branch proof,
not from a packet, installability premise, or assumed Joint. -/
theorem initial_joint : GeneralNominalJointCandidates.Joint registry start.current root declaration.id :=
  GeneralNominalJointCandidates.initial_joint registry context root declaration (by simp) checked rfl
    [(0,0)] rfl prepared model
    (GeneralDictionaryVariableTree.branch_models context registry root declaration checked shape model state_models)

theorem unrecorded : start.current.packets = [] := rfl

theorem reachable_unrecorded_nonterminal_joint :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    GeneralNominalJointCandidates.Joint registry start.current root declaration.id ∧
    start.current.packets = [] ∧ children ≠ [] :=
  ⟨actual_reachable,initial_models,initial_joint,unrecorded,inhabited_nonterminal.2.2⟩

theorem other_conflict : (report context leafDeclaration [(0,0)]).conflicts ≠ [] := by decide +kernel

theorem other_not_prepared
    (check : GeneralDeclarations.DeclarationChecked registry.constructors roles leafDeclaration) :
    ¬ Prepared registry context root leafDeclaration check := by
  rintro ⟨_,_,_,bounds,located,finished,_⟩
  have same : [(0,0)] = bounds := Option.some.inj located
  subst bounds
  exact other_conflict finished.2.1

theorem unique : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current root declaration.id children := by
  change Survivor registry context root declaration.id children ∧
    ∀ key kids, Survivor registry context root key kids → key = declaration.id ∧ kids = children
  refine ⟨survivor,?_⟩
  rintro key kids ⟨_,decl,visible,check,identity,_,bounds,located,ready,emitted⟩
  rcases List.mem_cons.mp visible with first | rest
  · subst decl
    have same : [(0,0)] = bounds := Option.some.inj located
    subst bounds
    exact ⟨identity.symm,emitted⟩
  · have same := List.mem_singleton.mp rest
    subst decl
    exact False.elim (other_not_prepared check ready)
end Yulang.GeneralDictionaryVariableTreeInitialJoint
