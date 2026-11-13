import Yulang.GeneralDictionaryProvenanceTreeBranch
import Yulang.GeneralDictionaryCoveredEvidence

/-! Conditional soundness of the actual Value classifier's entire recursive
payload. Coverage is syntax and operational request provenance for each selected
focus, not evidence or all-model branch validity. Deriving this coverage for
arbitrary reachable states remains open. -/
namespace Yulang.GeneralDictionaryProvenanceClassification
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence CommonRoleOutermostResolver
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
variable {roles : Roles.RoleDecls}

def Covered (registry : Registry) (root : Occurrence roles) (state : Tracked roles) : Prop :=
  ∀ focus key children, GeneralNominalValueBoundary.Local registry state focus (.selected key children) →
    ∃ chosen ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles chosen,
        ∃ shape : GeneralDictionaryHistoricalTreeBranch.Shape state.current.context registry focus chosen checked,
          GeneralDictionaryRequestProvenance.Supported registry root state
            (GeneralNominalMaterialization.requests state.current.context.state registry focus chosen checked
              (bindings state.current.context.state (report state.current.context chosen [(shape.slot,shape.slot)])))

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
      (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
      (covered : Covered registry root state)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionary : GeneralDictionaryReadback.Payload) (focus : Occurrence roles)
      (derived : B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
        registry state focus (.selected dictionary)) :
      Evidence registry state.current.context model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨children,safe,unique,classified⟩ :=
        GeneralDictionaryCoveredEvidence.classify_node_parts (v := GeneralNominalValueBoundary.vocabulary roles)
          (GeneralNominalValueBoundary.boundary roles).toSourceBoundary registry state focus key dictionaries derived
      have selected : GeneralNominalValueBoundary.Local registry state focus (.selected key children) :=
        (GeneralNominalValueBoundary.local_correspondence registry state focus _).mp
          (B4TargetV3.Local.selected safe unique)
      obtain ⟨chosen,visible,checked,shape,supported⟩ := covered focus key children selected
      exact GeneralDictionaryProvenanceTreeBranch.value_node_evidence registry root focus state reachable
        chosen visible checked shape supported key children selected model valid dictionaries
        (dictionaries_evidence registry root state reachable covered model valid dictionaries children classified)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
      (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
      (covered : Covered registry root state)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionaries : List GeneralDictionaryReadback.Payload) (focuses : List (Occurrence roles))
      (derived : All₂ (fun focus dictionary =>
        B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
          registry state focus (.selected dictionary)) focuses dictionaries) :
      All₂ (Evidence registry state.current.context model) focuses dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence registry root state reachable covered model valid _ _ first)
        (dictionaries_evidence registry root state reachable covered model valid _ _ rest)
  termination_by sizeOf dictionaries
end
end Yulang.GeneralDictionaryProvenanceClassification
