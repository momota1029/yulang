import Yulang.GeneralNominalValueObservation
import Yulang.GeneralNominalValueSteps

/-! Per-head support transport across actual updates. Source and discharged
explanations retain depth zero through every update constructor. Positive
provisional depths require a further installation/merge transport argument. -/
namespace Yulang.GeneralNominalValueBudget
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalValueSteps GeneralNominalValueDepth

variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {before after : Tracked roles}

theorem at_facts (update : At registry before focus after) :
    ∀ fact ∈ before.facts, fact ∈ after.facts := by
  intro fact member
  cases update with
  | administrative => exact member
  | install => exact List.mem_append_right _ member
  | merge => exact List.mem_append_right _ member

theorem at_slice (update : At registry before focus after)
    (support : List (Occurrence roles)) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Slice after support model) : Slice before support model := by
  have source := GeneralNominalSupportSteps.at_source
    (GeneralNominalDownstreamSteps.at_old (at_old update))
  exact ⟨source ▸ valid.1,fun fact member dependencies => valid.2 fact (at_facts update fact member) dependencies⟩

theorem at_head (update : At registry before focus after)
    (supported : HeadSupported before support identity test) : HeadSupported after support identity test := by
  obtain ⟨snapshot,observation,head,entailed⟩ := supported
  exact ⟨snapshot,observation,head,fun model valid => entailed model (at_slice update support model valid)⟩

theorem at_packets (update : At registry before focus after)
    (packet : Packet roles) (member : packet ∈ before.current.packets) : packet ∈ after.current.packets := by
  cases update with
  | administrative _ _ action => cases action <;> exact member
  | install => exact List.mem_cons_of_mem _ member
  | merge => exact member

theorem at_discharged (update : At registry before focus after)
    (done : Discharged before.current producer) : Discharged after.current producer := by
  have growth := (GeneralNominalReobservationSteps.at_extends
    (GeneralNominalSupportSteps.at_old (GeneralNominalDownstreamSteps.at_old (at_old update)))).journal
  induction done with
  | packet packet member _ ih => exact .packet packet (at_packets update packet member) ih
  | alias first last one two related _ ih =>
    exact .alias first last (growth.sites first one) (growth.sites last two)
      (GeneralNominalSaturationSteps.alias_monotone growth related) ih

theorem step_head (update : Step registry root before after)
    (supported : HeadSupported before support identity test) : HeadSupported after support identity test :=
  at_head update.choose_spec.2 supported

/-- This is an all-update per-head bound, not a bound on the producer pool. -/
theorem zero_depth_step (update : Step registry root before after)
    (known : HeadDepth registry before 0 identity test) : HeadDepth registry after 0 identity test := by
  obtain ⟨support,head,discharged⟩ := known
  exact ⟨support,step_head update head,fun producer member =>
    at_discharged update.choose_spec.2 (discharged producer member)⟩

theorem zero_depth_steps (path : B4Target.Steps (Step registry root) before after)
    (known : HeadDepth registry before 0 identity test) : HeadDepth registry after 0 identity test := by
  induction path with
  | refl => exact known
  | tail _ update ih => exact zero_depth_step update ih

end Yulang.GeneralNominalValueBudget
