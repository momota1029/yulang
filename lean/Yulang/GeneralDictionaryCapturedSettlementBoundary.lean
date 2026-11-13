import Yulang.GeneralDictionaryCapturedTrustedBoundary
import Yulang.GeneralDictionarySharedCapturedResumption

/-! The actual refreshed journal has not discharged its captured consumer.
Consequently no Trusted slice can contain the parent output, even though the
full journal semantically entails its alias. This rules out that particular
alias explanation, not every possible proof of ReadyAt. -/
namespace Yulang.GeneralDictionaryCapturedSettlementBoundary
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedProducer
open GeneralDictionarySharedCapturedResumption
open GeneralDeclarationExamples (roles)

theorem alias_eq_of_empty {roles : Roles.RoleDecls} {state : State roles} (empty : state.aliases = [])
    {first last : Nat} (same : Alias state first last) : first = last := by
  induction same with
  | refl => rfl
  | edge member => rw [empty] at member; cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem discharged_identity {roles : Roles.RoleDecls} {state : State roles} (empty : state.aliases = [])
    {occurrence : GeneralSourceDictionaries.Occurrence roles}
    (done : Discharged state occurrence) :
    ∃ p ∈ state.packets, p.site.occurrence.identity = occurrence.identity := by
  induction done with
  | packet p member _ _ => exact ⟨p,member,rfl⟩
  | alias first last _ _ same _ ih =>
    obtain ⟨p,member,equal⟩ := ih
    exact ⟨p,member,equal.trans (alias_eq_of_empty empty same)⟩

theorem trusted_output_settled {roles : Roles.RoleDecls} {state : Tracked roles} {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted state facts readbacks)
    {p : Packet roles} {support : List (GeneralSourceDictionaries.Occurrence roles)}
    (member : Fact.outputs p support ∈ facts) :
    GeneralNominalSettledSupport.PacketSettled state.current p := by
  induction trusted with
  | source => cases member
  | input packet support trusted present readback explanation ih =>
    simp only [List.mem_cons] at member
    rcases member with impossible | member
    · cases impossible
    · exact ih member
  | output packet support certificate target term trusted present input settled recipe ih =>
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · cases equal; exact settled
    · exact ih member
  | merge first last support trusted present evidence ih =>
    simp only [List.mem_cons] at member
    rcases member with impossible | member
    · cases impossible
    · exact ih member

theorem consumer_not_discharged : ¬ Discharged observed.current consumer := by
  intro done
  obtain ⟨p,member,equal⟩ := discharged_identity (state := observed.current) rfl done
  change p ∈ [candidate,packet] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · have different : candidate.site.occurrence.identity ≠ consumer.identity := by decide +kernel
    exact different equal
  · have different : packet.site.occurrence.identity ≠ consumer.identity := by decide +kernel
    exact different equal

theorem parent_not_trusted {facts : List (Fact roles)}
    {readbacks : GeneralNominalSharedSupport.Readbacks}
    (trusted : GeneralNominalSharedSupport.Trusted observed facts readbacks)
    (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    Fact.outputs packet support ∉ facts := by
  intro member
  exact consumer_not_discharged
    (GeneralDictionaryCapturedTrustedBoundary.parent_settlement_requires_consumer
      observed.current (trusted_output_settled trusted member))
end Yulang.GeneralDictionaryCapturedSettlementBoundary
