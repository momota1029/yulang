import Yulang.GeneralNominalCenteredLedgerPermutation

/-! Concrete transport of the three non-installation action families. Merges
retain the complete support-alternative ledger and every historical plan. -/
namespace Yulang.GeneralNominalLedgerPermutation.Related
open GeneralNominalSupport GeneralSourceDictionaries
variable {roles : Roles.RoleDecls}
    {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    {first last : Tracked roles}

theorem merge_guard (same : Related relation first last) (a b : GeneralNominalDemandMerging.Site roles) (support) :
    GeneralNominalSupportChoices.MergeGuard first a b support ↔ GeneralNominalSupportChoices.MergeGuard last a b support := by
  unfold GeneralNominalSupportChoices.MergeGuard GeneralNominalSupportChoices.RecoverySupported
  have slice := funext (fun model => propext (same.slice support model))
  rw [slice,same.current.recover,same.current.recover]

theorem merge_alternatives (same : Related relation first last) (a b : GeneralNominalDemandMerging.Site roles) :
    GeneralNominalSupportChoices.mergeAlternatives first a b = GeneralNominalSupportChoices.mergeAlternatives last a b := by
  classical
  unfold GeneralNominalSupportChoices.mergeAlternatives
  rw [same.pool]
  apply congrArg (List.filter · _)
  funext support
  exact decide_eq_decide.mpr (same.merge_guard a b support)

theorem merged_facts (same : Related relation first last) (a b : GeneralNominalDemandMerging.Site roles) :
    GeneralNominalSupportChoices.mergedFacts first a b = GeneralNominalSupportChoices.mergedFacts last a b := by
  unfold GeneralNominalSupportChoices.mergedFacts
  rw [same.merge_alternatives]

theorem merge (same : Related relation first last) (a b : GeneralNominalDemandMerging.Site roles) (support) :
    Related relation (GeneralNominalSharedSteps.merge first a b support) (GeneralNominalSharedSteps.merge last a b support) := by
  refine ⟨same.coherent,same.source,?_,same.recorded,?_⟩
  · exact ⟨⟨GeneralNominalMetadataEquivalence.extend same.current.context.state [] [] (fun _ => Iff.rfl) _,
      same.current.context.interpretation⟩,same.current.packets,same.current.sites,same.current.edges,
      congrArg (List.cons (a.occurrence.identity,b.occurrence.identity)) same.current.aliases⟩
  · change All₂ (FactPair relation) (GeneralNominalSupportChoices.mergedFacts first a b ++ first.facts)
      (GeneralNominalSupportChoices.mergedFacts last a b ++ last.facts)
    rw [same.merged_facts]
    have append : ∀ {a b c d}, All₂ (FactPair relation) a b → All₂ (FactPair relation) c d → All₂ (FactPair relation) (a ++ c) (b ++ d) := by
      intro a b c d pairs tail
      induction pairs with
      | nil => exact tail
      | cons pair pairs ih => exact .cons pair ih
    apply append _ same.facts
    unfold GeneralNominalSupportChoices.mergedFacts
    induction GeneralNominalSupportChoices.mergeAlternatives last a b with
    | nil => exact .nil
    | cons support tail ih => exact .cons .merge ih

theorem change_current (same : Related relation first last)
    (pair : GeneralNominalJournalPermutation.Related one two)
    (left : one.packets = first.current.packets) (right : two.packets = last.current.packets) :
    Related relation {first with current := one} {last with current := two} := by
  refine ⟨same.coherent,same.source,pair,?_,same.facts⟩
  intro a b related
  simpa only [left,right] using same.recorded related
end Yulang.GeneralNominalLedgerPermutation.Related

namespace Yulang.GeneralNominalCenteredLedgerPermutation.Related
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
variable {roles : Roles.RoleDecls}
    {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    {first last : State roles}

theorem administrative (same : Related relation first last)
    (action : GeneralNominalSharedSteps.Administrative registry first.erased.current focus next) (otherRegistry : Registry) :
    ∃ other, GeneralNominalSharedSteps.Administrative otherRegistry last.erased.current focus other ∧
      Related relation (GeneralNominalCenteredSteps.administrative first next) (GeneralNominalCenteredSteps.administrative last other) := by
  obtain ⟨other,step,pair⟩ := same.erased.current.administrative action otherRegistry
  have left : next.packets = first.erased.current.packets := by cases action <;> rfl
  have right : other.packets = last.erased.current.packets := by cases step <;> rfl
  exact ⟨other,step,⟨same.erased.change_current pair left right,same.sites,same.plans,same.roots⟩⟩

noncomputable def refresh_certificate (same : Related relation first last) (certificate : Refresh first context) : Refresh last context where
  refines := GeneralNominalMetadataEquivalence.refines_left same.erased.current.context.state certificate.refines
  interpretation := certificate.interpretation.trans same.erased.current.context.interpretation
  exact := fun model valid => certificate.exact model ((same.models model).mpr valid)
  support := fun source member => (GeneralNominalMetadataEquivalence.sources same.erased.current.context.state source).mp
    (certificate.support source member)

theorem refresh (same : Related relation first last) (context) :
    Related relation (GeneralNominalCenteredSteps.refresh first context) (GeneralNominalCenteredSteps.refresh last context) :=
  ⟨same.erased.change_current (same.erased.current.regenerate (GeneralNominalJournalPermutation.ContextPair.refl context)) rfl rfl,
    same.sites,same.plans,same.roots⟩

theorem merge (same : Related relation first last) (a b : GeneralNominalCenters.Site roles) (support) :
    Related relation (GeneralNominalCenteredSteps.merge first a b support) (GeneralNominalCenteredSteps.merge last a b support) :=
  ⟨same.erased.merge a.observed b.observed support,same.sites,same.plans,same.roots⟩

theorem merge_action (same : Related relation first last) (a b : GeneralNominalCenters.Site roles) (support)
    (one : a ∈ first.sites) (two : b ∈ first.sites)
    (inputs : GeneralNominalCenters.SameInputs (Models first) a b)
    (novel : ¬ GeneralNominalSaturationState.Alias first.erased.current a.occurrence.identity b.occurrence.identity)
    (guard : GeneralNominalSupportChoices.MergeGuard first.erased a.observed b.observed support) :
    At registry last a.occurrence (GeneralNominalCenteredSteps.merge last a b support) := by
  have models := funext (fun model => propext (same.models model))
  exact .merge a b support ((same.sites a).mp one) ((same.sites b).mp two) (models ▸ inputs)
    (fun alias => novel ((same.erased.current.alias _ _).mpr alias)) ((same.erased.merge_guard _ _ _).mp guard)


theorem at_transport_or_install (same : Related relation first last)
    (action : At registry first focus next) (otherRegistry : Registry) :
    (∃ other, At otherRegistry last focus other ∧ Related relation next other) ∨
      ∃ plan support, focus = plan.packet.site.occurrence ∧ next = install first plan support ∧
        GeneralNominalFeedbackSteps.Installable registry first.erased.current plan.packet ∧
        ¬ GeneralNominalFeedbackSteps.Committed first.erased.current plan.packet ∧ PacketGuard first plan support := by
  cases action with
  | administrative focus next action =>
    obtain ⟨other,action,pair⟩ := same.administrative action otherRegistry
    exact Or.inl ⟨_,.administrative focus other action,pair⟩
  | refresh focus context certificate source member unknown known =>
    exact Or.inl ⟨_,.refresh focus context (same.refresh_certificate certificate) source
      ((GeneralNominalMetadataEquivalence.sources same.erased.current.context.state source).mp member)
      (fun present => unknown ((GeneralNominalMetadataEquivalence.known same.erased.current.context.state source).mpr present)) known,
      same.refresh context⟩
  | install plan support enabled novel guard => exact Or.inr ⟨plan,support,rfl,rfl,enabled,novel,guard⟩
  | merge a b support one two inputs novel guard =>
    exact Or.inl ⟨_,same.merge_action a b support one two inputs novel guard,same.merge a b support⟩

end Yulang.GeneralNominalCenteredLedgerPermutation.Related
