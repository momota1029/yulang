import Yulang.GeneralNominalSharedSteps

/-! Existing certified trusted histories and their head explanations survive
actual Shared transitions. No arbitrary current-snapshot ReadyAt transport is
asserted; the immutable observation witness is retained instead. -/
namespace Yulang.GeneralDictionarySharedTrustTransport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSharedSupport GeneralNominalSharedSteps
variable {roles : Roles.RoleDecls} {registry : Registry} {before after : Tracked roles}
variable {focus root : Occurrence roles}

theorem at_source (update : At registry before focus after) : after.source = before.source := by
  cases update <;> rfl

theorem at_facts (update : At registry before focus after) :
    ∀ fact ∈ before.facts, fact ∈ after.facts := by
  intro fact member
  cases update with
  | administrative => exact member
  | install => exact List.mem_append_right _ member
  | merge => exact List.mem_append_right _ member

theorem at_packets (update : At registry before focus after) :
    ∀ packet ∈ before.current.packets, packet ∈ after.current.packets := by
  intro packet member
  cases update with
  | administrative _ _ action => cases action <;> exact member
  | install => exact List.mem_cons_of_mem _ member
  | merge => exact member

theorem at_sites (update : At registry before focus after) :
    ∀ site ∈ before.current.sites, site ∈ after.current.sites := by
  cases update with
  | administrative _ _ action =>
    exact (GeneralNominalReobservationSteps.at_extends
      (GeneralNominalSupportSteps.administrative_old action)).journal.sites
  | install => exact fun _ member => List.mem_append_left _ member
  | merge => exact fun _ member => member

theorem at_aliases (update : At registry before focus after) :
    ∀ pair ∈ before.current.aliases, pair ∈ after.current.aliases := by
  cases update with
  | administrative _ _ action =>
    exact (GeneralNominalReobservationSteps.at_extends
      (GeneralNominalSupportSteps.administrative_old action)).journal.aliases
  | install => exact fun _ member => member
  | merge => exact fun _ member => List.mem_cons_of_mem _ member

theorem at_alias (update : At registry before focus after)
    (related : Alias before.current first last) : Alias after.current first last := by
  induction related with
  | refl => exact .refl _
  | edge member => exact .edge (at_aliases update _ member)
  | symm _ ih => exact .symm ih
  | trans _ _ one two => exact .trans one two

theorem at_discharged (update : At registry before focus after)
    (done : Discharged before.current producer) : Discharged after.current producer := by
  induction done with
  | packet packet member _ ih => exact .packet packet (at_packets update _ member) ih
  | alias first last one two related _ ih =>
    exact .alias first last (at_sites update _ one) (at_sites update _ two) (at_alias update related) ih

theorem generated_at (update : At registry before focus after)
    (generated : Generated before.current root child) : Generated after.current root child := by
  induction generated with
  | root => exact .root
  | child _ member ih => exact .child ih (GeneralNominalSharedSteps.at_edges update _ member)
  | alias reached one two related ih =>
    exact .alias ih (at_sites update _ one) (at_sites update _ two) (at_alias update related)

theorem at_settled (update : At registry before focus after)
    (done : GeneralNominalSettledSupport.PacketSettled before.current packet) :
    GeneralNominalSettledSupport.PacketSettled after.current packet :=
  ⟨at_packets update _ done.1,fun child member => at_discharged update (done.2 child member)⟩

theorem trusted_monotone
    (source : after.source = before.source)
    (facts : ∀ fact ∈ before.facts, fact ∈ after.facts)
    (settlement : ∀ packet, GeneralNominalSettledSupport.PacketSettled before.current packet →
      GeneralNominalSettledSupport.PacketSettled after.current packet)
    (trusted : Trusted before ledger readbacks) : Trusted after ledger readbacks := by
  have models (entries : List (Fact roles)) :
      GeneralNominalSharedSupport.Models after entries = GeneralNominalSharedSupport.Models before entries := by
    funext model
    simp only [GeneralNominalSharedSupport.Models,GeneralNominalSettledSupport.Models,source]
  induction trusted with
  | source => exact .source
  | input packet support _ member readback explanation ih =>
    apply Trusted.input packet support ih (facts _ member)
    · simpa only [GeneralNominalSettledSupport.Readback,models] using readback
    · simpa only [InputExplanation,models] using explanation
  | output packet support certificate target term _ member included done recipe ih =>
    let transported : OutputCertificate after _ _ packet :=
      { substitution := certificate.substitution
        recipes := certificate.recipes
        inputs := by simpa only [models] using certificate.inputs
        binders := certificate.binders
        uses := by simpa only [models] using certificate.uses }
    exact .output packet support transported target term ih (facts _ member) included
      (settlement packet done) recipe
  | merge first last support _ member evidence ih =>
    apply Trusted.merge first last support ih (facts _ member)
    simpa only [models] using evidence

theorem trusted_at (update : At registry before focus after)
    (trusted : Trusted before ledger readbacks) : Trusted after ledger readbacks :=
  trusted_monotone (at_source update) (at_facts update) (fun _ => at_settled update) trusted

theorem trusted_steps (path : B4Target.Steps (Step registry root) before after)
    (trusted : Trusted before ledger readbacks) : Trusted after ledger readbacks := by
  induction path with
  | refl => exact trusted
  | tail _ update ih => exact trusted_at update.choose_spec.2 ih

theorem head_at (update : At registry before focus after)
    (known : GeneralNominalSharedSupport.HeadJustified before identity test) :
    GeneralNominalSharedSupport.HeadJustified after identity test := by
  obtain ⟨ledger,readbacks,trusted,snapshot,observation,head,entailed⟩ := known
  refine ⟨ledger,readbacks,trusted_at update trusted,snapshot,observation,head,?_⟩
  intro model valid
  apply entailed model
  simpa only [GeneralNominalSharedSupport.Models,GeneralNominalSettledSupport.Models,at_source update] using valid

theorem head_step (update : Step registry root before after)
    (known : GeneralNominalSharedSupport.HeadJustified before identity test) :
    GeneralNominalSharedSupport.HeadJustified after identity test :=
  head_at update.choose_spec.2 known

theorem head_steps (path : B4Target.Steps (Step registry root) before after)
    (known : GeneralNominalSharedSupport.HeadJustified before identity test) :
    GeneralNominalSharedSupport.HeadJustified after identity test := by
  induction path with
  | refl => exact known
  | tail _ update ih => exact head_step update ih

end Yulang.GeneralDictionarySharedTrustTransport
