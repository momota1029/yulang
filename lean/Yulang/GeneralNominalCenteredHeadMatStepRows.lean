import Yulang.GeneralNominalCenteredHeadMatStepCoverage
import Yulang.GeneralNominalCenteredHeadMatExamples
import Yulang.GeneralNominalCenteredHeadWFJoinLocal

set_option backward.isDefEq.respectTransparency false

/-! The formerly deferred multi-tag row has a complete corrected packet model
extending its well-formed source. This is packet assembly, not a Step trace. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepRows
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadWFJoinSource
open GeneralNominalCenteredHeadWFJoinLocal
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

private theorem head_model_of_source (assignment : Assignment)
    (sourceValid : GeneralNominalState.Models snapshot assignment) :
    GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(1,1)] assignment := by
  constructor
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨sourceValid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,normalizeArgs,normalize,
        variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]

theorem packet_from_equations (assignment : Assignment)
    (sourceValid : GeneralNominalState.Models snapshot assignment)
    (equations : (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds
      (GeneralNominalCenteredHeadMatEffects.variables plan assignment) assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment := by
  apply GeneralNominalCenteredHeadMatStepPackets.models_iff.mp
  refine ⟨head_model_of_source assignment sourceValid,
    point_root_holds _ root (fun _ => rfl) assignment,?_,?_,equations,?_⟩
  · intro name needed
    rcases needed with input | ⟨clause,member,within⟩
    · simp [Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at input
    · cases List.mem_singleton.mp member
      cases within
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen
      cases seen
      exact GeneralNominalCenteredTerminalForkSource.scalar assignment sourceValid 1 (by decide +kernel)
    · intro entry member; cases member
  · intro clause member valid
    cases List.mem_singleton.mp member
    constructor
    · intro index
      exact Fin.elim0 index
    · change ∀ equation ∈ (GeneralNominalCenteredHeadMatPlans.childSchema plan childClause valid).equations, _
      simp [GeneralNominalCenteredHeadMatPlans.childSchema,Plan.childRequests,List.ofFn_zero,
        GeneralNominalCenteredHeadMatSchemas.generated]

theorem source_packet_extension : ∃ assignment : Assignment,
    GeneralNominalCenteredHeadMatStepJournal.Models
      (GeneralNominalCenteredHeadMatStepJournal.initial context root) assignment ∧
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment ∧
    ∀ identity ∈ GeneralNominalState.sources snapshot, assignment identity = model identity := by
  obtain ⟨assignment,sourceValid,equations,kept⟩ := GeneralNominalCenteredHeadMatExamples.Rows.source_extension
  refine ⟨assignment,(GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr sourceValid,
    packet_from_equations assignment sourceValid ?_,kept⟩
  rw [GeneralNominalCenteredHeadMatExamples.Rows.schema_exact] at equations ⊢
  simpa only [GeneralNominalCenteredHeadMatSchemas.Schema.Holds,List.mem_singleton,forall_eq,
    GeneralNominalCenteredHeadMatSchemas.Equation.Holds,GeneralNominalCenteredHeadMatExpressions.value,
    GeneralNominalCenteredHeadMatExpressions.values,GeneralNominalCenteredHeadMatExpressions.primitiveValue] using equations

abbrev before : GeneralNominalCenteredHeadMatStepJournal.State roles :=
  GeneralNominalCenteredHeadMatStepJournal.initial context root

def effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles :=
  ⟨registry,before.core,plan,frame,unique,by
    intro output member
    change output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root at member
    rw [requests_empty] at member
    cases member⟩

def after := GeneralNominalCenteredHeadMatStepJournal.install before effect

theorem installed_parent_requests_empty : GeneralNominalCenteredHeadOutputs.requests after.core root = [] := by
  have invariant := GeneralNominalCenteredHeadMatStepRoles.install (plan := plan) (registry := registry)
    (GeneralNominalCenteredHeadMatStepRoles.initial context root) frame
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,alias,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  have colors := GeneralNominalCenteredHeadMatStepRoles.alias_color invariant alias
  rw [GeneralNominalCenteredHeadMatStepRoles.color_of_origin checked
    (show GeneralNominalCenteredHeadMatStepRoles.Origin registry snapshot.seed root root from Or.inl rfl),
    GeneralNominalCenteredHeadMatStepRoles.color_of_origin checked (invariant.raw site present)] at colors
  have declared := site.occurrence.demand.declared output within
  rw [← colors] at declared
  obtain ⟨body,impossible⟩ := declared
  cases impossible

theorem installed_journal_inhabited : ∃ assignment, GeneralNominalCenteredHeadMatStepJournal.Models after assignment := by
  obtain ⟨assignment,initialValid,branch,_⟩ := source_packet_extension
  apply GeneralNominalCenteredHeadMatStepJournal.installed_inhabited (effect := effect) rfl
  refine ⟨assignment,initialValid,branch,?_,?_,?_⟩
  · refine ⟨GeneralNominalCenteredHeadMatStepPackets.head_equations branch,?_,?_⟩
    · intro output member
      change output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root at member
      rw [requests_empty] at member
      cases member
    · intro output member
      change output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root at member
      rw [requests_empty] at member
      cases member
  · constructor <;> intro output member
    all_goals
      change output ∈ GeneralNominalCenteredHeadOutputs.requests after.core root at member
      rw [installed_parent_requests_empty] at member
      cases member
  · intro prior member; cases member

end Yulang.GeneralNominalCenteredHeadMatStepRows
