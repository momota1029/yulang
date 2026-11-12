import Yulang.GeneralDictionaryObservedScalarRequests
import Yulang.GeneralDictionarySupportOrdinaryExecution

/-! Source-observed output certificates survive actual ordinary-only traces.
No assertion is made for refresh or for requests at newly allocated targets. -/
namespace Yulang.GeneralDictionaryObservedRequestTransport
open GeneralDictionaryObservedScalarRequests GeneralNominalMaterialization
open GeneralDictionaryOrdinaryTrace

/-- A finite batch is observed precisely when both constituent batches are. -/
theorem observed_append (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (first last : List Request) :
    Observed state interpretation (first ++ last) ↔
      Observed state interpretation first ∧ Observed state interpretation last := by
  simp only [Observed, List.mem_append]
  constructor
  · intro h
    exact ⟨fun r m => h r (Or.inl m), fun r m => h r (Or.inr m)⟩
  · rintro ⟨one,two⟩ r (member | member)
    · exact one r member
    · exact two r member

/-- The entire observational certificate is unchanged, not merely its validity
in one model. Exact ordinary Extension excludes descriptor-changing updates. -/
theorem observed_extension (before after : GeneralNominalCandidates.Context)
    (growth : Extension before after) (requests : List Request) :
    Observed after.state after.interpretation requests ↔
      Observed before.state before.interpretation requests := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  rfl

/-- Actual support enqueue/equate/guarded-install/guarded-merge traces preserve
all named scalar request observations in either direction. -/
theorem observed_trace {roles : Roles.RoleDecls} (registry : GeneralDeclarations.Registry)
    (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root) before after)
    (requests : List Request) :
    Observed after.current.context.state after.current.context.interpretation requests ↔
      Observed before.current.context.state before.current.context.interpretation requests :=
  observed_extension _ _ (GeneralDictionarySupportOrdinaryExecution.steps_extension path) requests

/-- Any particular final source model satisfies the generated materialization
constraints. The initial certificate is structural, not a branch-model premise. -/
theorem generated_models_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.current.context.state before.current.context.interpretation requests)
    (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models after.current.context.state model) :
    Models after.current.context.state declaration capture report
      (generated after.current.context.state after.current.context.interpretation requests) model :=
  generated_models _ _ _ ((observed_trace registry root before after path requests).mpr observed)
    declaration capture report model valid
/-- Variable-only where inputs leave named root requests intact at the final
state. Captures and actual child generation are not erased; only materialization
requests are reduced using the separately proved VariableClauses condition. -/
theorem actual_requests_models_after_trace {roles : Roles.RoleDecls}
    (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root) before after)
    (declaration : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (observed : Observed before.current.context.state before.current.context.interpretation
      (rootRequests declaration root))
    (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models after.current.context.state model) :
    Models after.current.context.state declaration capture report
      (generated after.current.context.state after.current.context.interpretation
        (requests after.current.context.state registry root declaration checked captures)) model := by
  rw [requests_root _ _ _ _ _ _ variables]
  exact generated_models_after_trace registry root before after path _ observed
    declaration capture report model valid
end Yulang.GeneralDictionaryObservedRequestTransport
