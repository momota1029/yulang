import Yulang.GeneralDictionaryRecursiveEvidence
import Yulang.GeneralNominalCenteredHeadMatStepPackets

/-! Default-aware source evidence. The legacy partial inspection, materialization
completion and one-model branch constraints are retained. Only explicit-only
RootDefined is replaced by a provenance-bearing, total-expression output rule.
The actual input center is taken from the supplied source snapshot, not chosen
anew to make a default true. No selection or execution judgment is a premise. -/
namespace Yulang.GeneralDictionaryDefaultEvidence204
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload PayloadEvidence)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralNominalCenteredHeadMatEffects (compileBody BodyHolds)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls}

/-- A requested output retains its explicit/default source, successful total
translation, and equality in the same specified final model. -/
def OutputWitness (plan : Plan roles) (model : Assignment)
    (output : GeneralSourceState.Output) : Prop :=
  ∃ body, Supplies roles plan.packet.declaration output.name body ∧
    (∃ expression, compileBody plan body = some expression) ∧
    BodyHolds plan output.target model body

structure Certificate (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) (root : Occurrence roles) (key : Nat)
    (children : List (Occurrence roles)) (plan : Plan roles) : Prop where
  registry_eq : plan.packet.registry = registry
  context_eq : plan.packet.context = state.erased.current.context
  root_eq : plan.packet.site.occurrence = root
  key_eq : plan.packet.declaration.id = key
  visible : plan.packet.declaration ∈ registry.declarations
  role_eq : plan.packet.declaration.role = root.demand.role
  located : arguments plan.packet.context root = some plan.packet.bounds
  finished : Finished (report plan.packet.context plan.packet.declaration plan.packet.bounds)
  generated_ready : (generated plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration plan.packet.checked plan.packet.bounds).unknown = false
  children_eq : children = plan.packet.children
  metadata : Metadata registry state.erased.current.context
  branch : BranchModels plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration plan.packet.checked plan.packet.bounds model
  center_recorded : plan.input ∈ state.sites
  center_holds : plan.input.Holds model
  outputs : ∀ output ∈ root.demand.outputs, OutputWitness plan model output

def Instance (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) : LocalInstance roles :=
  fun root key children => ∃ plan, Certificate registry state model root key children plan

def Evidence (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) (root : Occurrence roles) (payload : Payload) : Prop :=
  ErasedEvidence (Instance registry state model) root payload

variable {registry : Registry} {state : GeneralNominalCenteredSteps.State roles}
  {model : Assignment} {root : Occurrence roles} {payload : Payload}
  {key : Nat} {children : List (Occurrence roles)} {dictionaries : List Payload}
  {plan : Plan roles}

theorem evidence_iff_payload : Evidence registry state model root payload ↔
    PayloadEvidence (Instance registry state model) root payload :=
  (GeneralDictionaryReadback.payload_iff_erased _ _ _).symm

theorem evidence_node (source : Instance registry state model root key children)
    (given : All₂ (Evidence registry state model) children dictionaries) :
    Evidence registry state model root (.node key dictionaries) :=
  GeneralDictionaryReadback.erased_evidence_node _ _ _ _ _ source given

theorem evidence_node_elim (evidence : Evidence registry state model root (.node key dictionaries)) :
    ∃ children, Instance registry state model root key children ∧
      All₂ (Evidence registry state model) children dictionaries := by
  have payload := evidence_iff_payload.mp evidence
  cases payload with
  | node source children =>
    have convert : ∀ {cs : List (Occurrence roles)} {ds : List Payload},
        All₂ (PayloadEvidence (Instance registry state model)) cs ds →
        All₂ (Evidence registry state model) cs ds := by
      intro cs ds given
      induction given with
      | nil => exact .nil
      | cons first rest ih => exact .cons (evidence_iff_payload.mpr first) ih
    exact ⟨_,source,convert children⟩

theorem evidence_leaf_iff : Evidence registry state model root (.node key []) ↔
    Instance registry state model root key [] := by
  constructor
  · intro evidence
    obtain ⟨children,source,given⟩ := evidence_node_elim evidence
    cases given
    exact source
  · intro source
    exact evidence_node source .nil

/-- The only missing legacy guard is explicit-body coverage: supplying it
recovers the entire old local judgment, with no lost branch or child premise. -/
theorem certificate_legacy (source : Certificate registry state model root key children plan)
    (explicit : GeneralNominalMaterialization.RootDefined plan.packet.declaration root) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.erased.current.context model root key children := by
  rcases plan with ⟨⟨reg,ctx,site,decl,checked,bounds⟩,input,input_exact⟩
  have regEq : reg = registry := source.registry_eq
  have ctxEq : ctx = state.erased.current.context := source.context_eq
  have rootEq : site.occurrence = root := source.root_eq
  subst reg; subst ctx
  refine ⟨decl,source.visible,checked,source.key_eq,source.role_eq,bounds,
    source.located,source.finished,⟨explicit,?_⟩,?_,source.metadata,?_⟩
  · simpa only [rootEq] using source.generated_ready
  · simpa only [GeneralNominalSaturationState.Packet.children,GeneralNominalSaturationState.Packet.bindings,rootEq]
      using source.children_eq
  · simpa only [rootEq] using source.branch

theorem instance_models (source : Instance registry state model root key children) :
    GeneralNominalState.Models state.erased.current.context.state model := by
  obtain ⟨plan,source⟩ := source
  have valid := (branch_interval_sound plan.packet.registry plan.packet.context plan.packet.site.occurrence
    plan.packet.declaration plan.packet.checked plan.packet.bounds model source.branch).1
  simpa only [source.context_eq] using valid

end Yulang.GeneralDictionaryDefaultEvidence204
