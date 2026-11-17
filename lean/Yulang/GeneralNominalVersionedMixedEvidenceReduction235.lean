import Yulang.GeneralNominalVersionedMixedCurrentCandidate235
set_option backward.isDefEq.respectTransparency false
/-! Conditional reductions, not proofs of the remaining availability premise.
EvidenceNode needs availability only in inhabited states; GeneratedChildren has
no model premise and is therefore stated separately with stronger availability. -/
namespace Yulang.GeneralNominalVersionedMixedEvidenceReduction235
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedCurrentCandidate235
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls}

abbrev Boundary (roles : Roles.RoleDecls) := GeneralNominalVersionedMixedSourceBoundary234.boundary roles

def Available (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (Boundary roles).Checked registry → ∀ state root demand key children,
    B4TargetV8.Reachable (Boundary roles) registry root state →
    (demand = root ∨ Generated state.core.erased.current root demand) →
    (Boundary roles).Stable registry state demand →
    GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children) →
    ∃ effect, Current (GeneralNominalCenteredHeadAllocEncoding.registry registry) state demand effect

def InhabitedAvailable (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (Boundary roles).Checked registry → ∀ state root demand key children,
    B4TargetV8.Reachable (Boundary roles) registry root state →
    (demand = root ∨ Generated state.core.erased.current root demand) →
    (Boundary roles).Stable registry state demand →
    GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children) →
    (∃ model, Models state model) →
    ∃ effect, Current (GeneralNominalCenteredHeadAllocEncoding.registry registry) state demand effect

theorem inhabited_of_available (available : Available roles) : InhabitedAvailable roles :=
  fun registry checked state root demand key children path reached stable selected _ =>
    available registry checked state root demand key children path reached stable selected

theorem evidenceNode (available : InhabitedAvailable roles) : B4SkeletonV8.EvidenceNode (Boundary roles) := by
  intro registry checked state root path model valid demand key children dictionaries reached stable _childStable selected childEvidence
  obtain ⟨effect,current⟩ := available registry checked state root demand key children path reached stable selected ⟨model,valid⟩
  exact GeneralNominalVersionedMixedStableEvidence235.selected_node stable
    (source_installable current path selected) current.occurrence_eq
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) valid childEvidence

theorem generatedChildren (available : Available roles) : B4SkeletonV8.GeneratedChildren (Boundary roles) := by
  intro registry checked state root demand key children path reached stable selected child member
  obtain ⟨effect,current⟩ := available registry checked state root demand key children path reached stable selected
  exact GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable
    (source_installable current path selected) current.occurrence_eq
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) reached member

theorem inhabited_generated_children (available : InhabitedAvailable roles)
    (checked : (Boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (Boundary roles) registry root state)
    (reached : demand = root ∨ Generated state.core.erased.current root demand)
    (stable : (Boundary roles).Stable registry state demand)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children))
    (inhabited : ∃ model, Models state model) (member : child ∈ children) :
    Generated state.core.erased.current root child := by
  obtain ⟨effect,current⟩ := available registry checked state root demand key children path reached stable selected inhabited
  exact GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable
    (source_installable current path selected) current.occurrence_eq
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected) reached member

theorem semantic_bridges (available : Available roles) :
    B4SkeletonV8.EvidenceNode (Boundary roles) ∧ B4SkeletonV8.GeneratedChildren (Boundary roles) :=
  ⟨evidenceNode (inhabited_of_available available),generatedChildren available⟩

end Yulang.GeneralNominalVersionedMixedEvidenceReduction235
