import Yulang.GeneralNominalRecordedNode194

/-! A finite readback-only catalogue extends recorded syntax with current
committed plans. It never changes the state used to interpret models. -/
namespace Yulang.GeneralNominalReuseCatalogue195
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryJournalTree (Covered Recorded Reach)
variable {roles : Roles.RoleDecls}

/-- Structural and nonrecursive semantic data for unrecorded reuse. No step,
installation certificate or dictionary evidence is assumed. -/
def Reusable (registry : Registry) (state : State roles) (plan : Plan roles) : Prop :=
  Frame registry state.core plan.packet.site.occurrence plan.packet.declaration.id plan ∧
  GeneralNominalRecursiveCandidates.RequestReady plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds ∧
  GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet

/-- Readback syntax only; this value is not asserted reachable and its Models
are never used to establish semantic soundness. -/
def catalogue (state : State roles) (plans : List (Plan roles)) : GeneralNominalSaturationState.State roles :=
  { state.core.erased.current with packets := state.core.erased.current.packets ++ plans.map (·.packet) }

variable {registry : Registry} {state : State roles} {plans : List (Plan roles)}
variable {root : Occurrence roles} {context : GeneralNominalCandidates.Context}

theorem reusable_instance {plan : Plan roles} (reuse : Reusable registry state plan)
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children :=
  GeneralNominalSemanticNode194.instance_of_frame reuse.1 reuse.2.1 model (reuse.2.2.1 model valid.1.1)

theorem packet_instance
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (ready : ∀ plan ∈ plans, Reusable registry state plan)
    (packet : GeneralNominalSaturationState.Packet roles)
    (member : packet ∈ (catalogue state plans).packets)
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  rcases List.mem_append.mp member with recorded | reusable
  · exact GeneralNominalOrdinaryJournal194.packet_instance path packet recorded model valid
  · obtain ⟨plan,present,rfl⟩ := List.mem_map.mp reusable
    exact reusable_instance (ready plan present) model valid

/-- No accessibility premise remains: finite packet syntax has increasing child IDs. -/
theorem uniform_dictionary
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (ready : ∀ plan ∈ plans, Reusable registry state plan)
    (covered : Covered (catalogue state plans) root) :
    ∃ tree : Dictionary roles, tree.root = root ∧
      GeneralSourceDictionaries.Evidence (Recorded (catalogue state plans)) tree ∧
      ∀ model, Models state model → (boundary roles).Evidence registry state model root (erase tree) := by
  obtain ⟨tree,same,syntactic⟩ := GeneralNominalJournalAccessibility194.recorded_tree _ root covered
  refine ⟨tree,same,syntactic,?_⟩
  intro model valid
  refine ⟨tree,⟨same,rfl⟩,?_⟩
  apply evidence_mono (Recorded (catalogue state plans))
    (GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model)
    (fun focus key children rule => ?_) syntactic
  obtain ⟨packet,member,rfl,rfl,rfl⟩ := rule
  exact packet_instance path ready packet member model valid

/-- The local evidence rule covers the unrecorded case and keeps all child
premises in the same original final model. -/
theorem evidence_node
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (ready : ∀ plan ∈ plans, Reusable registry state plan)
    {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}
    (recorded : ∃ packet ∈ (catalogue state plans).packets, packet.site.occurrence = focus)
    (selected : Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state model) (payloads : List Payload)
    (childEvidence : CommonRoleOutermostResolver.All₂ ((boundary roles).Evidence registry state model) children payloads) :
    (boundary roles).Evidence registry state model focus (.node key payloads) := by
  obtain ⟨packet,present,same⟩ := recorded
  have source := packet_instance path ready packet present model valid
  rw [same] at source
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children payloads
    (GeneralNominalSelectedJournal194.selected_instance selected model source).2.2 childEvidence
end Yulang.GeneralNominalReuseCatalogue195
