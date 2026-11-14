import Yulang.GeneralNominalLedgerPermutation

/-! Shared promotion reuses exactly the same readback terms and substitutions.
The paired journal changes packet records, never the readback identity. -/
namespace Yulang.GeneralNominalLedgerPermutation.Related
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {relation : Packet roles → Packet roles → Prop}
    {first last : Tracked roles}

theorem input_explanation (same : Related relation first last) (facts : All₂ (FactPair relation) one two)
    (pair : relation packet other) (explanation : GeneralNominalSharedSupport.InputExplanation first one packet) :
    GeneralNominalSharedSupport.InputExplanation last two other := by
  have paired := same.coherent.sound pair
  have source := funext (fun model => propext (same.models facts model))
  have input := funext (fun model => propext (paired.toPacketPair.inputs model))
  unfold GeneralNominalSharedSupport.InputExplanation at *
  simp only [← paired.input,← paired.captured,← source,← input]
  exact explanation

def output_certificate (same : Related relation first last) (facts : All₂ (FactPair relation) one two)
    (pair : relation packet other)
    (certificate : GeneralNominalSharedSupport.OutputCertificate first one readbacks packet) :
    GeneralNominalSharedSupport.OutputCertificate last two readbacks other where
  substitution := certificate.substitution
  recipes := by
    have paired := same.coherent.sound pair
    simpa only [GeneralNominalSharedSupport.Recipes,← paired.site,← paired.named] using certificate.recipes
  inputs := by
    have paired := same.coherent.sound pair
    have source := funext (fun model => propext (same.models facts model))
    have delta : GeneralNominalSharedSupport.Delta packet = GeneralNominalSharedSupport.Delta other :=
      funext fun model => propext (and_congr (paired.toPacketPair.inputs model) (paired.toPacketPair.outputs model))
    simp only [← paired.named,← paired.outputNames,← paired.captured,← source,← delta]
    exact certificate.inputs
  binders := by
    have paired := same.coherent.sound pair
    simpa only [← paired.named,← paired.outputNames,← paired.capture] using certificate.binders
  uses := by
    have paired := same.coherent.sound pair
    intro model valid delta entry member actual
    apply certificate.uses model ((same.models facts model).mpr valid)
      ⟨(paired.toPacketPair.inputs model).mpr delta.1,(paired.toPacketPair.outputs model).mpr delta.2⟩ entry
    · exact paired.named.symm ▸ member
    · exact actual

theorem shared_trusted {facts : List (Fact roles)} (same : Related relation first last)
    (trusted : GeneralNominalSharedSupport.Trusted first facts readbacks) :
    ∃ other, All₂ (FactPair relation) facts other ∧ GeneralNominalSharedSupport.Trusted last other readbacks := by
  induction trusted with
  | source => exact ⟨[],.nil,.source⟩
  | input packet support _ member readback explanation ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨fact,present,pair⟩ := all₂_left same.facts member
    cases pair with
    | inputs pair =>
      exact ⟨_,.cons (.inputs pair) pairs,.input _ support trusted present
        ((same.readback pairs pair).mp readback) (same.input_explanation pairs pair explanation)⟩
  | output packet support certificate target term _ member included settled recipe ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨fact,present,pair⟩ := all₂_left same.facts member
    cases pair with
    | outputs pair =>
      exact ⟨_,.cons (.outputs pair) pairs,.output _ support (same.output_certificate pairs pair certificate) target term
        trusted present ((same.coherent.fact_members pairs (.inputs pair)).mp included)
        ((same.packet_settled pair).mp settled) ((same.coherent.sound pair).named ▸ recipe)⟩
  | merge a b support _ member evidence ih =>
    obtain ⟨facts,pairs,trusted⟩ := ih
    obtain ⟨fact,present,pair⟩ := all₂_left same.facts member
    cases pair with
    | merge => exact ⟨_,.cons .merge pairs,.merge a b support trusted present ((same.merge_evidence pairs a b).mp evidence)⟩

end Yulang.GeneralNominalLedgerPermutation.Related
