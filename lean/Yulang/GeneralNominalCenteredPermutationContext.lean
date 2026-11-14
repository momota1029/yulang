import Yulang.GeneralNominalCenteredPermutationRepresentation

set_option backward.isDefEq.respectTransparency false

/-! Candidate applicability depends on the observation core and allocation
membership, so metadata enumeration does not change a private branch. -/
namespace Yulang.GeneralNominalCenteredPermutationContext
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalMetadataEquivalence (replace)

variable {roles : Roles.RoleDecls}

def context (old : Context) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat) : Context :=
  ⟨replace old.state allocated reserved,old.interpretation⟩

variable (old : Context) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

theorem report (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds old.state)) :
    GeneralNominalRecursiveCandidates.report (context old allocated reserved) declaration bounds =
      GeneralNominalReportMetadata.report old.state allocated reserved (GeneralNominalRecursiveCandidates.report old declaration bounds) := by
  unfold GeneralNominalRecursiveCandidates.report
  dsimp only [context]
  rw [GeneralNominalMetadataInspection.queries,← GeneralNominalReportMetadata.many]
  rfl

theorem branch (registry) (root : Occurrence roles) (declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) (bounds model) :
    BranchModels registry (context old allocated reserved) root declaration checked bounds model ↔
      BranchModels registry old root declaration checked bounds model :=
  GeneralNominalPacketMetadata.holds
    ⟨registry,old,GeneralNominalDemandMerging.pointSite root,declaration,checked,bounds⟩ allocated reserved model

theorem generated (registry) (root : Occurrence roles) (declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) (bounds) :
    GeneralNominalRecursiveCandidates.generated registry (context old allocated reserved) root declaration checked bounds =
      GeneralNominalRecursiveCandidates.generated registry old root declaration checked bounds :=
  GeneralNominalPacketMetadata.named_schema
    ⟨registry,old,GeneralNominalDemandMerging.pointSite root,declaration,checked,bounds⟩ allocated reserved

theorem children (registry) (root : Occurrence roles) (declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) (bounds) :
    GeneralNominalAllocation.children (context old allocated reserved).state registry root declaration checked
      (GeneralNominalRecursiveInspection.bindings _ (GeneralNominalRecursiveCandidates.report (context old allocated reserved) declaration bounds)) =
    GeneralNominalAllocation.children old.state registry root declaration checked
      (GeneralNominalRecursiveInspection.bindings _ (GeneralNominalRecursiveCandidates.report old declaration bounds)) :=
  GeneralNominalPacketMetadata.children
    ⟨registry,old,GeneralNominalDemandMerging.pointSite root,declaration,checked,bounds⟩ allocated reserved

theorem private_models (registry) (root : Occurrence roles) (declaration bounds model) :
    GeneralNominalState.Models (privateState registry (context old allocated reserved) root declaration bounds) model ↔
      GeneralNominalState.Models (privateState registry old root declaration bounds) model := by
  unfold privateState
  rw [GeneralNominalState.extend_models,GeneralNominalState.extend_models,
    GeneralNominalAllocation.propagate_models,GeneralNominalAllocation.propagate_models,report]
  simp only [context,GeneralNominalReportMetadata.bindings,GeneralNominalReportMetadata.selfChecks]
  rfl

variable (same : GeneralNominalMetadataEquivalence.Same old.state (replace old.state allocated reserved))
include same

theorem prepared (registry) (root : Occurrence roles) (declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) :
    Prepared registry (context old allocated reserved) root declaration checked ↔ Prepared registry old root declaration checked := by
  have metadata : Metadata registry (context old allocated reserved) ↔ Metadata registry old := Iff.rfl
  have linked : GeneralNominalState.Linked (context old allocated reserved).state root.demand ↔ GeneralNominalState.Linked old.state root.demand :=
    (GeneralNominalMetadataEquivalence.linked same root.demand).symm
  have fresh : GeneralNominalAllocation.Fresh (context old allocated reserved).state registry root.identity ↔ GeneralNominalAllocation.Fresh old.state registry root.identity :=
    (GeneralNominalMetadataEquivalence.fresh same registry root.identity).symm
  simp only [Prepared,metadata,linked,fresh,RequestReady,Consistent,branch,generated,report,GeneralNominalReportMetadata.finished]
  rfl

theorem failed (registry) (root : Occurrence roles) (declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) :
    Failed registry (context old allocated reserved) root declaration checked ↔ Failed registry old root declaration checked := by
  have metadata : Metadata registry (context old allocated reserved) ↔ Metadata registry old := Iff.rfl
  have fresh : GeneralNominalAllocation.Fresh (context old allocated reserved).state registry root.identity ↔ GeneralNominalAllocation.Fresh old.state registry root.identity :=
    (GeneralNominalMetadataEquivalence.fresh same registry root.identity).symm
  simp only [Failed,metadata,fresh,RequestReady,Consistent,branch,generated,report,GeneralNominalReportMetadata.report]
  rfl

theorem head_ready (registry) (root : Occurrence roles) (declaration) :
    HeadReady registry (context old allocated reserved) root declaration ↔ HeadReady registry old root declaration := by
  have metadata : Metadata registry (context old allocated reserved) ↔ Metadata registry old := Iff.rfl
  have linked : GeneralNominalState.Linked (context old allocated reserved).state root.demand ↔ GeneralNominalState.Linked old.state root.demand :=
    (GeneralNominalMetadataEquivalence.linked same root.demand).symm
  have fresh : GeneralNominalAllocation.Fresh (context old allocated reserved).state registry root.identity ↔ GeneralNominalAllocation.Fresh old.state registry root.identity :=
    (GeneralNominalMetadataEquivalence.fresh same registry root.identity).symm
  simp only [HeadReady,metadata,linked,fresh,private_models,report,GeneralNominalReportMetadata.finished]
  simp only [context,GeneralNominalReportMetadata.projectionModels]
  rfl

theorem survivor (registry) (root : Occurrence roles) (key kids) :
    Survivor registry (context old allocated reserved) root key kids ↔ Survivor registry old root key kids := by
  simp only [Survivor,prepared old allocated reserved same,children old allocated reserved]
  rfl

theorem inspection_pending (registry) (root : Occurrence roles) :
    InspectionPending registry (context old allocated reserved) root ↔ InspectionPending registry old root := by
  simp only [InspectionPending,failed old allocated reserved same,prepared old allocated reserved same]
  rfl

end Yulang.GeneralNominalCenteredPermutationContext
