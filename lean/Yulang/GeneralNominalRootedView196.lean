import Yulang.GeneralNominalVariableView196

set_option backward.isDefEq.respectTransparency false
/-! Reinspection only at keys and bounds used by a finite source dictionary.
The support certificate is structural, not a semantic evidence premise. -/
namespace Yulang.GeneralNominalRootedView196
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalViewTransport196
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {registry : Registry}
variable {old : GeneralNominalCandidates.Context} {next : View old.state}

/-- Only selected keys and actual lookup bounds; no global report agreement. -/
def AtNode (registry : Registry) (old : GeneralNominalCandidates.Context)
    (next : View old.state) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key →
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments old root = some bounds →
      Rechecked old next declaration bounds

inductive Support (registry : Registry) (old : GeneralNominalCandidates.Context)
    (next : View old.state) : Dictionary roles → Prop where
  | node (atNode : AtNode registry old next root key)
      (children : ∀ child ∈ trees, Support registry old next child) :
      Support registry old next (.node root key trees)

theorem node_transport (agreement : AtNode registry old next root key)
    (model : Assignment) (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralDictionaryRecursiveEvidence.Instance registry old model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (context old next) model root key children := by
  obtain ⟨decl,visible,checked,identity,role,bs,located,finished,ready,kids,metadata,branch⟩ := source
  have same := agreement decl visible identity bs located
  refine ⟨decl,visible,checked,identity,role,bs,located,?_,?_,?_,metadata,?_⟩
  · rw [same]; exact finished
  · unfold GeneralNominalRecursiveCandidates.RequestReady at ready ⊢
    rw [generated_eq same]; exact ready
  · rw [same]
    simp only [context,bindings_report]
    exact kids
  · exact branch_transport same registry root checked model valid branch

/-- The structural finite-tree certificate, rather than a global local-rule
implication, controls the induction. All children remain in the same model. -/
theorem tree_transport (support : Support registry old next tree)
    (model : Assignment) (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry old model) tree) :
    GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry (context old next) model) tree := by
  induction support with
  | node atNode children ih =>
    cases source with
    | node rule allChildren =>
      exact .node (node_transport atNode model valid rule)
        (fun child member => ih child member (allChildren child member))

theorem readback_transport (support : Support registry old next tree)
    (readback : Readback root payload tree)
    (model : Assignment) (valid : GeneralNominalState.Models (replace old.state next) model)
    (source : GeneralSourceDictionaries.Evidence
      (GeneralDictionaryRecursiveEvidence.Instance registry old model) tree) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (context old next) model root payload :=
  ⟨tree,readback,tree_transport support model valid source⟩

/-- A local syntactic check discharges only this node's selected-key reports. -/
theorem node_of_variables (root : Occurrence roles) (key : Nat)
    (shape : ∀ declaration ∈ registry.declarations, declaration.id = key →
      ∃ names : List (List Nat), GeneralNominalInspection.queries old.state old.interpretation declaration =
        names.map GeneralNominalInspection.Query.variables) : AtNode registry old next root key := by
  intro declaration member identity bounds _
  obtain ⟨names,same⟩ := shape declaration member identity
  exact GeneralNominalVariableView196.rechecked_variables old next declaration names same bounds

/-- Existing registry-wide certificates are sufficient but no longer required. -/
theorem support_of_global (agreement : Rechecks registry old next) (tree : Dictionary roles) :
    Support registry old next tree := by
  cases tree with
  | node root key children =>
    apply Support.node (fun declaration member _ bounds _ => agreement declaration member bounds)
    intro child member
    exact support_of_global agreement child
termination_by sizeOf tree
decreasing_by
  have bound := List.sizeOf_lt_of_mem member
  simp_all
  omega
end Yulang.GeneralNominalRootedView196
