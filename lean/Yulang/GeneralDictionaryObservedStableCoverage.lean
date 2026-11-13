import Yulang.GeneralDictionaryObservedAliasJoint
import Yulang.GeneralDictionaryVariableStableCoverage
import Yulang.GeneralDictionaryCoveredEvidence

/-! Observed scalar named-output coverage at a stable state of an actual ordinary trace. Joint
and descendant generation are derived; neither is a coverage assumption. -/
namespace Yulang.GeneralDictionaryObservedStableCoverage
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
      ∃ checked : DeclarationChecked registry.constructors roles chosen,
      GeneralDictionaryObservedAliasJoint.Shape state.current.context registry focus chosen checked ∧
      GeneralDictionaryObservedAliasJoint.Covered registry state focus chosen checked


/-- Ordinary initial traces supply source formation and packet extension. The
named-output syntax constructs Joint; Joint is not an input hypothesis. -/
theorem initial_trace_joint (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : GeneralDictionaryObservedAliasJoint.Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : GeneralDictionaryObservedAliasJoint.Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalJointCandidates.Joint registry state.current focus key :=
  GeneralDictionaryObservedAliasJoint.covered_joint registry root focus state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (GeneralDictionarySupportOrdinaryExecution.initial_packets_extension registry root context state path)
    chosen visible checked shape key children selected covered model valid

/-- After deriving Joint independently in one model, actual stability provides
Instance in every current model and generation of the actual selected children. -/
theorem stable_instances_generated (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : GeneralDictionaryObservedAliasJoint.Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : GeneralDictionaryObservedAliasJoint.Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (stable : Stable registry state focus) :
    (∀ assignment, Models state.current assignment →
      Instance registry state.current.context assignment focus key children) ∧
      ∀ child ∈ children, Generated state.current focus child := by
  have reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state :=
    ⟨GeneralNominalSupport.initial context root,⟨context,source,rfl⟩,
      GeneralDictionarySupportOrdinaryExecution.steps_actual path⟩
  exact GeneralDictionarySupportEvidence.reachable_joint_instance registry state root focus reachable key children
    stable selected (initial_trace_joint registry root focus context source state path chosen visible checked
      shape key children selected covered model valid)

/-- Existing variable-tree coverage is included, so named-output coverage is
an extension rather than a replacement of the prior conditional theorem. -/
theorem covered_of_variable (registry : Registry) (state : Tracked roles)
    (root : Occurrence roles)
    (covered : GeneralDictionaryVariableStableCoverage.Covered registry state root) :
    Covered registry state root := by
  intro focus reached key children selected
  rcases covered focus reached key children selected with historical | structural
  · exact Or.inl historical
  · obtain ⟨chosen,visible,checked,shape,aliases⟩ := structural
    refine Or.inr ⟨chosen,visible,checked,Or.inr shape,?_⟩
    intro site related
    obtain ⟨localShape,localSelected⟩ := aliases site related
    exact ⟨Or.inr localShape,localSelected⟩

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
    have result := stable_instances_generated registry root focus
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
/-- Conditional dictionary soundness at the actual root for every current
model. This is not general B4 DictionarySound: ordinary trace, stability and
structural coverage are explicit hypotheses, and a finite Classify is given. -/
theorem root_dictionary_all_models (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (stable : Stable registry state root) (covered : Covered registry state root)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    ∀ model, Models state.current model →
      Evidence registry state.current.context model root dictionary := by
  intro model valid
  exact dictionary_evidence registry root context source state path stable covered model valid
    dictionary root .root derived

/-- Coverage can be restricted to any generated descendant; the originating
ordinary trace and initial root need not be changed. -/
theorem covered_descendant (registry : Registry) (state : Tracked roles)
    (root focus : Occurrence roles) (covered : Covered registry state root)
    (reached : Generated state.current root focus) : Covered registry state focus := by
  intro child descendant key children selected
  exact covered child (generated_trans reached descendant) key children selected

end Yulang.GeneralDictionaryObservedStableCoverage
