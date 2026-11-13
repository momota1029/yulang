import Yulang.GeneralNominalActualBoundary
import Yulang.GeneralNominalPatersonLineage

/-! Every selected Actual child has a checked syntactic descent schema.
This does not construct coherent labels across edges, a root-relative rank,
actual installation guards, or where-tree accessibility. -/
namespace Yulang.GeneralDictionaryActualEdge173
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalFeedbackSites (clauseChild)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}
variable {parent child : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

theorem selected_child_schema
    (selected : GeneralNominalActualBoundary.Local registry state parent (.selected key children))
    (member : child ∈ children) :
    ∃ packet : Packet roles, ∃ clause : Clause, ∃ signature : clause.Signature roles,
      packet.registry = registry ∧ packet.context = state.current.context ∧
      packet.site.occurrence = parent ∧ packet.declaration.id = key ∧
      child = clauseChild packet clause signature ∧
      clause ∈ packet.declaration.requirements ∧
      ∀ capture : Nat → Pattern,
        mass (substArgs capture clause.arguments) < mass (substArgs capture packet.declaration.head) := by
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context parent key children := by
    cases selected with
    | selected _ unique => exact unique.1
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,emitted⟩ := survivor
  let packet : Packet roles := ⟨registry,state.current.context,
    GeneralNominalDemandMerging.pointSite parent,declaration,checked,bounds⟩
  have present : child ∈ packet.children := by
    change child ∈ GeneralNominalAllocation.children state.current.context.state registry parent declaration checked
      (GeneralNominalRecursiveInspection.bindings state.current.context.state
        (GeneralNominalRecursiveCandidates.report state.current.context declaration bounds))
    rw [← emitted]
    exact member
  obtain ⟨clause,clausePresent,signature,same⟩ :=
    GeneralNominalPatersonLineage.emitted_clause packet child present
  refine ⟨packet,clause,signature,rfl,rfl,rfl,identity,same,clausePresent,?_⟩
  intro capture
  exact (checked_child_descent packet.checked clause clausePresent capture).1

end Yulang.GeneralDictionaryActualEdge173
