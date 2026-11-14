import Yulang.GeneralNominalCanonicalHoleJournal
import Yulang.GeneralNominalReducedHoleSources

/-! Uniform semantic readbacks and exact source labels are transported as
one object. Materialized outputs reuse a single substitution for every input
capture and prior output binder; their newly allocated identities add no leaf. -/
namespace Yulang.GeneralNominalUniformHoleLabels
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalOpenPatternLabels GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination
open GeneralNominalSaturationState GeneralNominalActualInspectionSteps GeneralNominalCanonicalHoleJournal
open GeneralNominalMaterialization

def Labelled (models : GeneralNominalCommonBridge.Assignment → Prop)
    (context : GeneralNominalCandidates.Context) (origins : Nat → Origin) (remaining : List Nat)
    (root : Origin) (pattern : Pattern) (term : Expr Nat) : Prop :=
  Label context pattern term ∧ Readback models origins remaining root term

theorem alias_labelled (known : Labelled models context origins remaining first pattern term)
    (same : ∀ model, models model → Same model first last) :
    Labelled models context origins remaining last pattern term :=
  ⟨known.1,alias known.2 same⟩

theorem restrict_labelled (known : Labelled before context origins remaining root pattern term)
    (restriction : ∀ model, after model → before model) :
    Labelled after context origins remaining root pattern term :=
  ⟨known.1,restrict known.2 restriction⟩

theorem step_labelled (step : Step registry focus before after)
    (known : Labelled (Models before.current) context origins remaining root pattern term) :
    Labelled (Models after.current) context origins remaining root pattern term :=
  ⟨known.1,step_preserves step known.2⟩

theorem replace_labelled (known : Labelled models context origins remaining root pattern term)
    (replacement : Labelled models context origins (remaining.erase hole) (origins hole) value tree) :
    Labelled models context origins (remaining.erase hole) root
      (normalize (pattern.subst (patternReplacement hole value))) (replace hole tree term) :=
  ⟨filled_label known.1 _ _ (replacement_images replacement.1),eliminate_readback known.2 replacement.2⟩

theorem restrict_replace_all {relevant : Origin → Pattern → Expr Nat → Prop}
    (restriction : ∀ model, after model → before model)
    (known : ∀ root pattern term, relevant root pattern term →
      Labelled before context origins remaining root pattern term)
    (replacement : Labelled after context origins (remaining.erase hole) (origins hole) value tree) :
    ∀ root pattern term, relevant root pattern term →
      Labelled after context origins (remaining.erase hole) root
        (normalize (pattern.subst (patternReplacement hole value))) (replace hole tree term) :=
  fun root pattern term recorded => replace_labelled (restrict_labelled (known root pattern term recorded) restriction) replacement

/-- The same source-key substitution updates all relevant meanings, including
old packet inputs and retained materialized outputs. -/
theorem actual_replace {relevant : Origin → Pattern → Expr Nat → Prop}
    (step : Step registry focus before after)
    (known : ∀ root pattern term, relevant root pattern term →
      Labelled (Models before.current) context origins remaining root pattern term)
    (replacement : Labelled (Models after.current) context origins (remaining.erase hole) (origins hole) value tree) :
    ∀ root pattern term, relevant root pattern term →
      Labelled (Models after.current) context origins (remaining.erase hole) root
        (normalize (pattern.subst (patternReplacement hole value))) (replace hole tree term) :=
  restrict_replace_all (GeneralNominalSharedSteps.step_models (step_shared step)) known replacement

/-- Two distinct surviving holes with the same actual meaning merge by
replacing one with the other. This consumes a hole and introduces no node. -/
theorem alias_replacement {remaining : List Nat} {origins : Nat → Origin} (survives : other ∈ remaining) (distinct : other ≠ hole)
    (same : ∀ model, models model → Same model (origins hole) (origins other)) :
    Labelled models context origins (remaining.erase hole) (origins hole) (.var other) (.leaf other) := by
  refine ⟨⟨rfl,?_,True.intro⟩,same,?_⟩
  · simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote]
  · intro name member
    cases List.mem_singleton.mp member
    exact (List.mem_erase_of_ne distinct).mpr survives

/-- A labelled actual schema recipe produces a uniform labelled output.
Input and binder premises concern actual origins over the same surviving
source holes; none is a model-dependent choice of a finite expression. -/
theorem materialized_labelled (recipe : Recipe body (.source target) openTerm)
    (template : Label context pattern openTerm)
    (valid : ∀ model, models model → GeneralNominalMaterialization.Models state declaration capture report body model)
    (substitution : Nat → Pattern) (trees : Nat → Expr Nat)
    (labels : ∀ name, Label context (substitution name) (trees name))
    (inputs : ∀ entry ∈ body.variables, entry.mode = .actual → entry.name ∉ declaration.outputNames →
      ∃ captured ∈ report.captures, captured.name = entry.name ∧ ∃ root,
        captured.origin = some root ∧ Readback models origins remaining root (trees entry.name))
    (binders : ∀ entry ∈ body.variables, entry.mode = .actual → entry.name ∈ declaration.outputNames →
      Readback models origins remaining (.source (capture.outputs entry.name)) (trees entry.name)) :
    Labelled models context origins remaining (.source target)
      (normalize (pattern.subst substitution)) (openTerm.bind trees) :=
  ⟨filled_label template substitution trees labels,
    GeneralNominalIndexedOutputProduction.materialized_output recipe valid trees inputs binders⟩

/-- These are the semantic and historical sides of the same replacement.
The resulting packet capture labels and origin meanings use identical source
substitution, with exact normalized child syntax retained by the journal. -/
theorem replacement_coherent {relevant : Origin → Pattern → Expr Nat → Prop}
    (step : Step registry focus before after)
    (journal : Journal context root before inventory)
    (known : ∀ origin pattern term, relevant origin pattern term →
      Labelled (Models before.current) context origins inventory.holes origin pattern term)
    (replacement : Labelled (Models after.current) context origins (inventory.holes.erase hole) (origins hole) value tree)
    (extra : Nat) :
    Nonempty (Journal context root before (eliminate inventory hole (GeneralNominalPatternInventory.encode value) extra)) ∧
      ∀ origin pattern term, relevant origin pattern term →
        Labelled (Models after.current) context origins (inventory.holes.erase hole) origin
          (normalize (pattern.subst (patternReplacement hole value))) (replace hole tree term) :=
  ⟨⟨journal.replace replacement.1 hole extra⟩,actual_replace step known replacement⟩

/-- A certified eliminating branch of the actual transition. In addition to
the local replacement, the installing packet must have a simultaneous match
against the transformed historical labels. -/
theorem actual_eliminating_install {relevant : Origin → Pattern → Expr Nat → Prop}
    (step : Step registry focus before after)
    (installed : after = GeneralNominalSharedSteps.install before packet support)
    (journal : Journal context root before inventory)
    (known : ∀ origin pattern term, relevant origin pattern term →
      Labelled (Models before.current) context origins inventory.holes origin pattern term)
    (replacement : Labelled (Models after.current) context origins (inventory.holes.erase hole) (origins hole) value tree)
    (present : hole ∈ inventory.holes)
    (closed : Closed (inventory.holes.erase hole) (GeneralNominalPatternInventory.encode value))
    (bounded : GeneralNominalSharedEnumeration.Bounded (inventory.holes.erase hole) tests extra
      (GeneralNominalPatternInventory.encode value))
    (presented : packet.declaration.requirements ≠ [] → Nonempty
      (GeneralNominalCanonicalPacketTransport.Presentation context
        (GeneralNominalCanonicalPacketTransport.substituteLabels journal.labels (patternReplacement hole value)) packet)) :
    Trace tests (fun _ => extra) inventory
      (eliminate inventory hole (GeneralNominalPatternInventory.encode value) extra) 1 ∧
    Nonempty (Journal context root after
      (eliminate inventory hole (GeneralNominalPatternInventory.encode value) extra)) ∧
    ∀ origin pattern term, relevant origin pattern term →
      Labelled (Models after.current) context origins (inventory.holes.erase hole) origin
        (normalize (pattern.subst (patternReplacement hole value))) (replace hole tree term) := by
  obtain ⟨trace,updated⟩ := eliminating_install journal replacement.1 present closed bounded packet support presented
  refine ⟨trace,?_,actual_replace step known replacement⟩
  rw [installed]
  exact updated

theorem alias_eliminating_install {relevant : Origin → Pattern → Expr Nat → Prop}
    (step : Step registry focus before after)
    (installed : after = GeneralNominalSharedSteps.install before packet support)
    (journal : Journal context root before inventory)
    (known : ∀ origin pattern term, relevant origin pattern term →
      Labelled (Models before.current) context origins inventory.holes origin pattern term)
    (present : hole ∈ inventory.holes) (survives : other ∈ inventory.holes) (distinct : other ≠ hole)
    (same : ∀ model, Models after.current model → Same model (origins hole) (origins other))
    (presented : packet.declaration.requirements ≠ [] → Nonempty
      (GeneralNominalCanonicalPacketTransport.Presentation context
        (GeneralNominalCanonicalPacketTransport.substituteLabels journal.labels (patternReplacement hole (.var other))) packet)) :
    Trace tests (fun _ => 0) inventory (eliminate inventory hole (.leaf other) 0) 1 ∧
    Nonempty (Journal context root after (eliminate inventory hole (.leaf other) 0)) ∧
    ∀ origin pattern term, relevant origin pattern term →
      Labelled (Models after.current) context origins (inventory.holes.erase hole) origin
        (normalize (pattern.subst (patternReplacement hole (.var other)))) (replace hole (.leaf other) term) := by
  have member : other ∈ inventory.holes.erase hole := (List.mem_erase_of_ne distinct).mpr survives
  have closed : Closed (inventory.holes.erase hole) (GeneralNominalPatternInventory.encode (.var other)) := by
    intro name present
    cases List.mem_singleton.mp present
    exact member
  exact actual_eliminating_install step installed journal known (alias_replacement survives distinct same)
    present closed (.leaf other 0 member) presented

/-- Retained observations and aliases do not consume a hole. This branch
applies to every actual transition with an unchanged historical packet list. -/
theorem actual_retained {relevant : Origin → Pattern → Expr Nat → Prop}
    (step : Step registry focus before after)
    (unchanged : after.current.packets ⊆ before.current.packets)
    (journal : Journal context root before inventory)
    (known : ∀ origin pattern term, relevant origin pattern term →
      Labelled (Models before.current) context origins inventory.holes origin pattern term) :
    Trace tests (fun _ => 0) inventory inventory 0 ∧ Nonempty (Journal context root after inventory) ∧
      ∀ origin pattern term, relevant origin pattern term →
        Labelled (Models after.current) context origins inventory.holes origin pattern term :=
  ⟨.refl _,⟨journal.retain unchanged⟩,fun origin pattern term recorded => step_labelled step (known origin pattern term recorded)⟩

end Yulang.GeneralNominalUniformHoleLabels
