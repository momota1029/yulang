import Yulang.GeneralDictionaryFirstOwnership228

namespace Yulang.GeneralDictionaryFirstExtreme228
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227
open GeneralDictionaryResidualOwnership228 (LocalMerge)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls}

/-- The exceptional foreign capture has its actual origin observation at top
(lower endpoint) or bottom (upper endpoint). No equality of raw syntax is claimed. -/
def Extreme (plan : Plan roles) (model : Assignment) (identity : Nat) : Prop :=
  ∃ captured ∈ (headInspection plan).captures, ∃ origin, ∃ actual,
    captured.origin = some origin ∧ Observes model origin actual ∧
    ((identity = plan.packet.context.state.base.source captured.bounds.1 ∧
      CommonNominalFullCarrier.Subtype .top actual) ∨
     (identity = plan.packet.context.state.base.source captured.bounds.2 ∧
      CommonNominalFullCarrier.Subtype actual .bottom))

theorem owned_or_extreme
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (nonzero : identity ≠ 0) (absent : identity ∉ pool)
    (owned : GeneralDictionaryCapturedOwnership228.Owned plan identity) :
    LocalMerge plan identity ∨ Extreme plan model identity := by
  classical
  by_cases localName : LocalMerge plan identity
  · exact Or.inl localName
  · exact Or.inr (GeneralDictionaryCapturedOwnership228.owned_absent_nonlocal_extreme
      trace plan frame model valid schema nonzero absent owned localName)

/-- Every first protected p0/p1 has an actual enabled installation and its
common model. A foreign first read is necessarily an extremal captured value.
This does not rule out that exception or prove same-key extrema replay. -/
theorem first_local_or_extreme
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (trace : Footprint registry context root state pool)
    (mergePurpose : purpose = 0 ∨ purpose = 1)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈ pool) :
    ∃ before prior, ∃ effect : Effect roles, ∃ model : Assignment,
      Footprint registry context root before prior ∧
      fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
      Installable registry before effect ∧ Models before model ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧
      Contribution registry root before (install before effect)
        (GeneralDictionaryOriginJournal227.installDelta before effect) ∧
      (LocalMerge effect.plan (fresh context.state.seed invocation declaration purpose owner position) ∨
        Extreme effect.plan model (fresh context.state.seed invocation declaration purpose owner position)) ∧
      B4Target.Steps (Step registry root) (install before effect) state := by
  obtain ⟨before,prior,effect,history,absent,enabled,event,owned,suffix⟩ :=
    GeneralDictionaryFirstOwnership228.first_owned source trace mergePurpose present
  obtain ⟨model,valid,packet,_⟩ := enabled.common
  have result := owned_or_extreme history effect.plan (GeneralDictionaryDefaultDepth208.frame enabled)
    model valid (GeneralNominalCenteredHeadMatStepPackets.head_equations packet).2.2
    GeneralDictionaryBodyProvenance227.fresh_ne_zero absent owned
  exact ⟨before,prior,effect,model,history,absent,enabled,valid,packet,event,result,suffix⟩
end Yulang.GeneralDictionaryFirstExtreme228
