import Yulang.GeneralDictionaryTotalEvidence206
import Yulang.GeneralNominalCenteredHeadMatStepKernel

namespace Yulang.GeneralDictionaryDefaultSchema208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

/-- Preserve the requested name and target together with the selected RHS source. -/
structure Entry where
  output : GeneralSourceState.Output
  body : Option Body

noncomputable def entries (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) : List Entry :=
  (GeneralNominalCenteredHeadOutputs.requests state root).map
    fun output => ⟨output,lookup roles plan.packet.declaration output.name⟩

def Entry.Holds (plan : Plan roles) (model : Assignment) (entry : Entry) : Prop :=
  ∀ body, entry.body = some body → BodyHolds plan entry.output.target model body

def SchemaHolds (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles) (model : Assignment) : Prop :=
  (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds (variables plan model) model ∧
  (∀ entry ∈ entries state root plan, entry.Holds plan model) ∧
  GeneralNominalCenteredHeadOutputs.EqualOutputs state root model

variable {state : GeneralNominalCenteredSteps.State roles} {root : Occurrence roles}
  {plan : Plan roles} {model : Assignment}

theorem mem_entries : entry ∈ entries state root plan ↔
    ∃ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
      entry = ⟨output,lookup roles plan.packet.declaration output.name⟩ := by
  simp only [entries,List.mem_map]
  constructor
  · rintro ⟨output,member,equal⟩; exact ⟨output,member,equal.symm⟩
  · rintro ⟨output,member,equal⟩; exact ⟨output,member,equal.symm⟩

theorem entries_holds_iff :
    (∀ entry ∈ entries state root plan, entry.Holds plan model) ↔
    ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
      ∀ body, lookup roles plan.packet.declaration output.name = some body →
        BodyHolds plan output.target model body := by
  constructor
  · intro valid output member body found
    exact valid _ (mem_entries.mpr ⟨output,member,rfl⟩) body found
  · intro valid entry member
    obtain ⟨output,present,rfl⟩ := mem_entries.mp member
    exact valid output present

theorem schema_holds_iff : SchemaHolds state root plan model ↔
    (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds (variables plan model) model ∧
    ClassEffects state root plan model := by
  exact and_congr_right fun _ => and_congr_left fun _ => entries_holds_iff

theorem entry_provenance (member : entry ∈ entries state root plan)
    (found : entry.body = some body) :
    Supplies roles plan.packet.declaration entry.output.name body := by
  obtain ⟨output,_,rfl⟩ := mem_entries.mp member
  exact (lookup_exact roles plan.packet.declaration plan.packet.checked.identified.2.2.1 _ _).mp found

theorem entries_ready (ready : Ready state root plan)
    (member : entry ∈ entries state root plan) :
    ∃ body, entry.body = some body ∧ (bodySchema plan entry.output.target body).unknown = false := by
  obtain ⟨output,present,rfl⟩ := mem_entries.mp member
  exact ready output present

/-- Equal-named aliases retain all RHS equations, even if one side has no original output. -/
theorem alias_entries (alias : GeneralNominalSaturationState.Alias state.erased.current first.identity last.identity) :
    entry ∈ entries state first plan ↔ entry ∈ entries state last plan := by
  simp only [mem_entries,GeneralNominalCenteredHeadOutputs.same_class_requests alias]

end Yulang.GeneralDictionaryDefaultSchema208
