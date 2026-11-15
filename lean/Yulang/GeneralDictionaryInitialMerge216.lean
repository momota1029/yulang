import Yulang.GeneralDictionaryLiveSupport216

/-! The initial-source case discharges merge-slot freshness from the actual
below-seed invariant. No freshness premise is added to the initial domain. -/
namespace Yulang.GeneralDictionaryInitialMerge216
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalAllocation
open GeneralNominalAllocationSupport GeneralDictionaryMergeSlots216
open GeneralDictionaryMergeCompletion216
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {root : Occurrence roles}

theorem separation (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings) :
    Separate context.state registry invocation declaration bindings (GeneralNominalState.sources context.state) := by
  have outside (purpose : Nat) (i : Fin (active declaration bindings).length) :
      names context.state registry invocation declaration bindings purpose i ∉ GeneralNominalState.sources context.state := by
    intro member
    have below := source.below_seed _ member
    have above := GeneralNominalIdentities.source_above_seed context.state.seed
      (origin invocation declaration.id purpose (active declaration bindings)[i] 0)
    change context.state.seed < names context.state registry invocation declaration bindings purpose i at above
    omega
  exact fun i => ⟨outside 0 i,outside 1 i⟩

theorem complete (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (supported : Endpoints bindings (GeneralNominalState.sources context.state))
    (previous : Assignment) (valid : GeneralNominalState.Models context.state previous)
    (compatible : Compatible bindings previous) :
    ∃ extended, GeneralNominalState.Models (propagate context.state registry invocation declaration bindings) extended ∧
      ∀ name ∈ GeneralNominalState.sources context.state, extended name = previous name := by
  let extended := patch context.state registry invocation declaration bindings previous
  have separate := separation source invocation declaration bindings
  exact ⟨extended,propagation separate supported (fun _ h => h) previous valid compatible,
    preserves separate previous⟩

theorem satisfiable_iff (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (invocation : Nat) (declaration : Declaration) (bindings : Bindings)
    (supported : Endpoints bindings (GeneralNominalState.sources context.state)) :
    (∃ model, GeneralNominalState.Models (propagate context.state registry invocation declaration bindings) model) ↔
      ∃ model, GeneralNominalState.Models context.state model ∧ Compatible bindings model := by
  constructor
  · rintro ⟨model,valid⟩
    have parts := (propagate_models ..).mp valid
    exact ⟨model,parts.1,parts.2.1⟩
  · rintro ⟨model,valid,compatible⟩
    obtain ⟨extended,valid,_⟩ := complete source invocation declaration bindings supported model valid compatible
    exact ⟨extended,valid⟩

end Yulang.GeneralDictionaryInitialMerge216
