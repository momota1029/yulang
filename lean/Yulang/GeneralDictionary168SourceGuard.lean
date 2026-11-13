import Yulang.GeneralDictionarySharedEvidenceTrace
import Yulang.GeneralDictionarySharedTrustTransport
import Yulang.GeneralDictionarySharedSiblingPrefix

/-! Actual Shared traces that only extend ordinary constraints preserve trusted
readiness. Descriptor-changing refresh is not covered. No new execution or
stability judgment is introduced. -/
namespace Yulang.GeneralDictionary168SourceGuard
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSharedSupport
open GeneralDictionaryOrdinaryTrace (Extension extendContext)
open GeneralDictionaryOrdinaryTransport (extendState)
open GeneralDictionarySharedEvidenceTrace (OrdinaryStep)

 theorem head_extension {before after : GeneralNominalCandidates.Context}
    (growth : Extension before after) (head : Head before.state identity test observation) :
    Head after.state identity test observation := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  cases head with
  | scalar slot base seen => exact Head.scalar (snapshot := (extendContext before reserved atoms allocated).state) slot base seen
  | structural slot kind children seen => exact Head.structural (snapshot := (extendContext before reserved atoms allocated).state) slot kind children seen
  | nominal slot descriptor seen => exact Head.nominal (snapshot := (extendContext before reserved atoms allocated).state) slot descriptor seen

 theorem ready_steps {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles}
    (path : B4Target.Steps (OrdinaryStep registry root) before after)
    (ready : GeneralNominalSharedSupport.ReadyAt before identity) :
    GeneralNominalSharedSupport.ReadyAt after identity := by
  obtain ⟨test,observation,head,justified⟩ := ready
  exact ⟨test,observation,
    head_extension (GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path) head,
    GeneralDictionarySharedTrustTransport.head_steps
      (GeneralDictionarySharedEvidenceTrace.ordinary_trace_real _ _ _ _ path) justified⟩

mutual
 theorem reads_extended (snapshot : GeneralNominalState.State) (reserved atoms allocated)
    (query : GeneralNominalInspection.Query) (bounds : GeneralNominalInspection.Bounds snapshot) :
    reads (extendState snapshot reserved atoms allocated) query bounds = reads snapshot query bounds := by
  cases query with
  | variables names => simp only [reads.eq_def]
  | deferred term => simp only [reads.eq_def]
  | scalar base => simp only [reads.eq_def]
  | node shape patterns =>
    have ih := readsMany_extended snapshot reserved atoms allocated patterns
    simp only [reads.eq_def,extendState]
    repeat' split
    all_goals simp only [ih]
  | nominal name patterns =>
    have ih := readsMany_extended snapshot reserved atoms allocated patterns
    simp only [reads.eq_def,extendState]
    repeat' split
    all_goals simp only [ih]
 termination_by sizeOf query
 theorem readsMany_extended (snapshot : GeneralNominalState.State) (reserved atoms allocated)
    (queries : List GeneralNominalInspection.Query) (bounds : List (GeneralNominalInspection.Bounds snapshot)) :
    readsMany (extendState snapshot reserved atoms allocated) queries bounds = readsMany snapshot queries bounds := by
  cases queries with
  | nil => cases bounds <;> simp only [readsMany.eq_def]
  | cons query queries =>
    cases bounds with
    | nil => simp only [readsMany.eq_def]
    | cons bound bounds =>
      rw [readsMany.eq_def,readsMany.eq_def]
      dsimp only
      rw [reads_extended snapshot reserved atoms allocated query bound,
        readsMany_extended snapshot reserved atoms allocated queries bounds]
 termination_by sizeOf queries
end

 theorem decision_steps {roles : Roles.RoleDecls} {registry : Registry} {root consumer : Occurrence roles}
    {before after : Tracked roles}
    (path : B4Target.Steps (OrdinaryStep registry root) before after)
    (guard : GeneralNominalSharedSupport.DecisionGuard registry before consumer) :
    GeneralNominalSharedSupport.DecisionGuard registry after consumer := by
  have growth := GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path
  obtain ⟨reserved,atoms,allocated,same⟩ := growth
  unfold GeneralNominalSharedSupport.DecisionGuard
  rw [same]
  constructor
  · intro index
    exact ready_steps path (guard.1 index)
  · intro declaration visible role bounds located slot member
    have locatedOld : GeneralNominalRecursiveCandidates.arguments before.current.context consumer = some bounds := located
    have memberOld : slot ∈ readsMany before.current.context.state
        (GeneralNominalInspection.queries before.current.context.state before.current.context.interpretation declaration) bounds := by
      simpa only [extendContext,readsMany_extended,GeneralNominalInspection.queries] using member
    exact ready_steps path (guard.2 declaration visible role bounds locatedOld slot memberOld)

/-- All-model evidence survives the same real restricted trace, together with
its decision guard. Models may be lost to added constraints, so no final
inhabitation is claimed without a model witness. -/
theorem evidence_and_guard_steps {roles : Roles.RoleDecls} {registry : Registry}
    {root consumer : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (OrdinaryStep registry root) before after)
    (guard : GeneralNominalSharedSupport.DecisionGuard registry before consumer)
    (payload : GeneralDictionaryReadback.Payload)
    (evidence : ∀ model, Models before.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry before.current.context model consumer payload) :
    GeneralNominalSharedSupport.DecisionGuard registry after consumer ∧
    ∀ model, Models after.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model consumer payload := by
  refine ⟨decision_steps path guard,?_⟩
  intro model valid
  exact GeneralDictionaryOrdinaryTrace.evidence_extension registry _ _
    (GeneralDictionarySharedEvidenceTrace.ordinary_trace_extension _ _ _ _ path) model valid.1 consumer payload
    (evidence model (GeneralDictionarySharedEvidenceTrace.trace_models _ _ _ _
      (GeneralDictionarySharedEvidenceTrace.ordinary_trace_real _ _ _ _ path) model valid))

open GeneralNominalSupportSiblings
open GeneralDictionarySharedTerminalInstallation (after)

theorem container_install_ordinary : OrdinaryStep reg root afterP after :=
  ⟨GeneralDictionarySharedTerminalInstallation.step,
    GeneralDictionarySharedCurrentEvidence.private_extension
      GeneralNominalDownstreamSiblingFixture.containerPacket []⟩

theorem source_consumer_guard : GeneralNominalSharedSupport.DecisionGuard reg after kidC :=
  decision_steps (.tail .refl container_install_ordinary)
    GeneralDictionarySharedTerminalInstallation.container_decision

/-- Every ordinary-context Shared continuation of this actual positive source
fixture retains both the consumer guard and its exact terminal payload. -/
theorem source_consumer_continuation (last : Tracked GeneralDeclarationExamples.roles)
    (path : B4Target.Steps (OrdinaryStep reg root) after last) :
    GeneralNominalSharedSupport.DecisionGuard reg last kidC ∧
    ∀ model, Models last.current model →
      GeneralDictionaryRecursiveEvidence.Evidence reg last.current.context model kidC (.node c.id []) :=
  evidence_and_guard_steps path source_consumer_guard (.node c.id [])
    GeneralDictionarySharedTerminalInstallation.current_dictionary

/-- The positive case is inhabited and source-formed; it is not the unsupported
captured scalar input of the cycle167 regression. -/
theorem source_consumer_nonvacuous :
    GeneralNominalSharedSteps.SourceFormed reg root after ∧
    GeneralNominalSharedSupport.DecisionGuard reg after kidC ∧
    ∃ model, Models after.current model ∧
      GeneralDictionaryRecursiveEvidence.Evidence reg after.current.context model kidC (.node c.id []) := by
  obtain ⟨model,valid⟩ := GeneralDictionarySharedTerminalInstallation.inhabited
  exact ⟨GeneralDictionarySharedSiblingPrefix.shared_formed,source_consumer_guard,
    model,valid,GeneralDictionarySharedTerminalInstallation.current_dictionary model valid⟩
end Yulang.GeneralDictionary168SourceGuard
