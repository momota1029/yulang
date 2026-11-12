import Yulang.GeneralDictionaryUnrecordedVariableJoint
import Yulang.GeneralDictionaryCoveredEvidence

/-! Structural coverage at a stable state of an actual ordinary trace. Joint
and descendant generation are derived; neither is a coverage assumption. -/
namespace Yulang.GeneralDictionaryVariableStableCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalSupportBoundary
open GeneralDictionaryRecursiveEvidence CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

/-- All unrecorded selected focuses and their alias sites have actual syntax
for one visible checked declaration. Outputs/compound where patterns remain
restricted by Shape. Historical focuses need only actual packet membership. -/
def Covered (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ key children,
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
    (∃ packet ∈ state.current.packets, packet.site.occurrence = focus) ∨
    ∃ chosen ∈ registry.declarations,
      DeclarationChecked registry.constructors roles chosen ∧
      GeneralDictionaryUnrecordedVariableJoint.Shape state.current.context focus chosen ∧
      GeneralDictionaryUnrecordedVariableJoint.Covered registry state focus chosen

theorem stable_descendant (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles) (stable : Stable registry state root)
    (reached : Generated state.current root focus) : Stable registry state focus :=
  fun child descendant after => stable child (generated_trans reached descendant) after

/-- Syntax constructs the common model first. Stability then gives actual
child generation; we do not identify selected children with recorded children
before deriving Joint. -/
theorem selected_instance_children (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (stable : Stable registry state root) (covered : Covered registry state root)
    (reached : Generated state.current root focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children ∧
      ∀ child ∈ children, Generated state.current root child := by
  rcases covered focus reached key children selected with historical | structural
  · obtain ⟨packet,member,same⟩ := historical
    exact ⟨(GeneralDictionarySupportOrdinaryExecution.initial_selected_replay registry root focus context
      source state path packet member same key children selected model valid).2.2,
      (GeneralDictionarySupportOrdinaryExecution.initial_selected_generated registry root focus context
      source state path packet member same key children selected model valid).2⟩
  · obtain ⟨chosen,visible,checked,shape,aliases⟩ := structural
    have result := GeneralDictionaryUnrecordedVariableJoint.stable_instances_generated registry root focus
      context source state path chosen visible checked shape key children selected aliases model valid
      (stable_descendant registry state root focus stable reached)
    exact ⟨result.1 model valid,fun child member => generated_trans reached (result.2 child member)⟩

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles)
      (context : GeneralNominalCandidates.Context)
      (source : GeneralNominalSourceFormation.InitialSource registry context root)
      (state : Tracked roles)
      (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
        (GeneralNominalSupport.initial context root) state)
      (stable : Stable registry state root) (covered : Covered registry state root)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionary : GeneralDictionaryReadback.Payload) (focus : Occurrence roles)
      (reached : Generated state.current root focus)
      (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
        registry state focus (.selected dictionary)) :
      Evidence registry state.current.context model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨childrenList,safe,unique,children⟩ := GeneralDictionaryCoveredEvidence.classify_node_parts
        (v := GeneralNominalSupportBoundary.vocabulary roles)
        (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus key dictionaries derived
      have selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key _) :=
        (local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique)
      have result := selected_instance_children registry root focus context source state path stable covered
        reached key childrenList selected model valid
      exact evidence_node registry state.current.context model focus key childrenList dictionaries result.1
        (dictionaries_evidence registry root context source state path stable covered model valid _ _ result.2 children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles)
      (context : GeneralNominalCandidates.Context)
      (source : GeneralNominalSourceFormation.InitialSource registry context root)
      (state : Tracked roles)
      (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
        (GeneralNominalSupport.initial context root) state)
      (stable : Stable registry state root) (covered : Covered registry state root)
      (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
      (dictionaries : List GeneralDictionaryReadback.Payload) (demands : List (Occurrence roles))
      (reached : ∀ focus ∈ demands, Generated state.current root focus)
      (derived : All₂ (fun focus dictionary => B4TargetV3.Classify
        (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus (.selected dictionary))
        demands dictionaries) :
      All₂ (Evidence registry state.current.context model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence registry root context source state path stable covered model valid _ _
        (reached _ (by simp)) first)
        (dictionaries_evidence registry root context source state path stable covered model valid _ _
          (fun focus member => reached focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end
end Yulang.GeneralDictionaryVariableStableCoverage
