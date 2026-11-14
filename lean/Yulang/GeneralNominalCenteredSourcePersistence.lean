import Yulang.GeneralNominalCenteredProgress

/-! Existing source explanations survive every full centered transition.
The model predicate for trusted inputs remains source plus trusted facts;
this transport does not produce coverage for newly relevant captures. -/
namespace Yulang.GeneralNominalCenteredSourcePersistence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalSharedSupport GeneralNominalSupport

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

theorem packets_step (step : Step registry root before after) :
    before.erased.current.packets ⊆ after.erased.current.packets := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action => cases action <;> exact fun _ member => member
  | refresh | merge => exact fun _ member => member
  | install => exact fun _ member => List.mem_cons_of_mem _ member

theorem facts_step (step : Step registry root before after) : before.erased.facts ⊆ after.erased.facts := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative | refresh => exact fun _ member => member
  | merge | install => exact fun _ member => List.mem_append_right _ member

theorem discharged_step (step : Step registry root before after)
    (done : Discharged before.erased.current occurrence) : Discharged after.erased.current occurrence := by
  have growth := (GeneralNominalCenteredProgress.at_extends step.choose_spec.2).journal
  induction done with
  | packet packet member children ih => exact .packet packet (packets_step step member) ih
  | alias first last one two equal previous ih =>
    exact .alias first last (growth.sites _ one) (growth.sites _ two)
      (GeneralNominalSaturationSteps.alias_monotone growth equal) ih

theorem settled_step (step : Step registry root before after)
    (done : GeneralNominalSettledSupport.PacketSettled before.erased.current packet) :
    GeneralNominalSettledSupport.PacketSettled after.erased.current packet :=
  ⟨packets_step step done.1,fun child member => discharged_step step (done.2 child member)⟩

theorem coarse_models (step : Step registry root before after) (facts : List (Fact roles)) :
    GeneralNominalSharedSupport.Models after.erased facts = GeneralNominalSharedSupport.Models before.erased facts := by
  funext model
  simp only [GeneralNominalSharedSupport.Models,GeneralNominalSettledSupport.Models,
    (GeneralNominalCenteredTrace.source_step step).1]

theorem trusted_step (step : Step registry root before after)
    (trusted : Trusted before.erased facts readbacks) : Trusted after.erased facts readbacks := by
  have modelMap (facts : List (Fact roles)) (model : GeneralNominalCommonBridge.Assignment)
      (valid : GeneralNominalSharedSupport.Models after.erased facts model) :
      GeneralNominalSharedSupport.Models before.erased facts model := by
    rw [coarse_models step] at valid
    exact valid
  induction trusted with
  | source => exact .source
  | input packet support previous recorded readback explanation ih =>
    refine .input packet support ih (facts_step step recorded) ?_ ?_
    · intro slot visited test observation head model valid
      exact readback slot visited test observation head model (modelMap _ model valid)
    · intro entry member actual
      obtain ⟨origin,captured,same⟩ := explanation entry member actual
      exact ⟨origin,GeneralNominalCommonTrustedLedger.captured_restrict captured
        (fun model valid => ⟨modelMap _ model valid.1,valid.2⟩),
        fun model valid inputs => same model (modelMap _ model valid) inputs⟩
  | output packet support certificate target term previous recorded included settled recipe ih =>
    let transported : OutputCertificate after.erased _ _ packet := {
      substitution := certificate.substitution
      recipes := certificate.recipes
      inputs := by
        intro entry member actual notOutput
        obtain ⟨origin,same,captured⟩ := certificate.inputs entry member actual notOutput
        exact ⟨origin,same,GeneralNominalCommonTrustedLedger.captured_restrict captured
          (fun model valid => ⟨modelMap _ model valid.1,valid.2⟩)⟩
      binders := certificate.binders
      uses := fun model valid delta => certificate.uses model (modelMap _ model valid) delta }
    exact .output packet support transported target term ih (facts_step step recorded) included
      (settled_step step settled) recipe
  | merge first last support previous recorded evidence ih =>
    exact .merge first last support ih (facts_step step recorded)
      (GeneralNominalCommonTrustedLedger.merge_weaken evidence (modelMap _))

theorem trusted_inputs_step (step : Step registry root before after)
    (inputs : GeneralNominalSourceProducerHandoff.TrustedInputs before.erased facts context origins remaining keys tests) :
    GeneralNominalSourceProducerHandoff.TrustedInputs after.erased facts context origins remaining keys tests := by
  intro actual member
  obtain ⟨value,vocabulary⟩ := inputs actual member
  refine ⟨value.restrict ?_,vocabulary⟩
  intro model valid
  rw [coarse_models step] at valid
  exact valid

theorem trusted_inputs_trace (path : B4Target.Steps (Step registry root) before after)
    (inputs : GeneralNominalSourceProducerHandoff.TrustedInputs before.erased facts context origins remaining keys tests) :
    GeneralNominalSourceProducerHandoff.TrustedInputs after.erased facts context origins remaining keys tests := by
  induction path with
  | refl => exact inputs
  | tail path step ih => exact trusted_inputs_step step ih

theorem initial_trusted_empty
    (trusted : Trusted (GeneralNominalCenteredSteps.initial context (root : Occurrence roles)).erased facts readbacks) :
    facts = [] ∧ readbacks = [] := by
  cases trusted with
  | source => exact ⟨rfl,rfl⟩
  | input packet support previous recorded readback explanation => cases recorded
  | output packet support certificate target term previous recorded included settled recipe => cases recorded
  | merge first last support previous recorded evidence => cases recorded

theorem initial_trusted_inputs
    (trusted : Trusted (GeneralNominalCenteredSteps.initial context (root : Occurrence roles)).erased facts readbacks) :
    GeneralNominalSourceProducerHandoff.TrustedInputs
      (GeneralNominalCenteredSteps.initial context root).erased facts context origins remaining keys tests := by
  have empty := (initial_trusted_empty trusted).1
  subst facts
  intro actual member
  cases member

end Yulang.GeneralNominalCenteredSourcePersistence
