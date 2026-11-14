import Yulang.GeneralNominalCaptureFamilies

/-! New child labels are constructed from one simultaneous capture. Unique
clause allocation resolves collisions within the new packet. Reused historical
occurrences retain an explicit source-syntax agreement obligation. -/
namespace Yulang.GeneralNominalPacketChildLabels
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalCanonicalHoleJournal
open GeneralNominalCanonicalPacketTransport GeneralNominalSourceProducerHandoff
open GeneralNominalOriginTerms GeneralNominalOpenPatternLabels GeneralNominalHeadMatchMass
open GeneralNominalSubtermOrder GeneralNominalMatchedAssembly
open GeneralNominalFeedbackSites GeneralNominalCompatibleJournalExtension

variable {roles : Roles.RoleDecls}
variable {root : Occurrence roles} {before : GeneralNominalSupport.Tracked roles}

theorem identified {items : List α} {key : α → β}
    (unique : (items.map key).Nodup) (one : first ∈ items) (two : last ∈ items)
    (same : key first = key last) : first = last := by
  induction items with
  | nil => cases one
  | cons head tail ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp one with rfl | inFirst
    · rcases List.mem_cons.mp two with rfl | inLast
      · rfl
      · exact False.elim (parts.1 (List.mem_map.mpr ⟨last,inLast,same.symm⟩))
    · rcases List.mem_cons.mp two with rfl | inLast
      · exact False.elim (parts.1 (List.mem_map.mpr ⟨first,inFirst,same⟩))
      · exact ih parts.2 inFirst inLast

theorem child_clause (packet : Packet roles)
    (one : first ∈ packet.declaration.requirements) (two : last ∈ packet.declaration.requirements)
    (firstSignature : first.Signature roles) (lastSignature : last.Signature roles)
    (same : clauseChild packet first firstSignature = clauseChild packet last lastSignature) : first = last := by
  have numeric := congrArg Occurrence.identity same
  have allocated : GeneralNominalIdentities.source packet.context.state.seed
      (GeneralNominalAllocation.origin packet.site.occurrence.identity packet.declaration.id 6 first.id 0) =
      GeneralNominalIdentities.source packet.context.state.seed
      (GeneralNominalAllocation.origin packet.site.occurrence.identity packet.declaration.id 6 last.id 0) := numeric
  have tuple := (GeneralNominalIdentities.source_identity _ _ _).mp allocated
  exact identified packet.checked.identified.1 one two (congrArg (fun key => key.2.2.2.1) tuple)

def Protected (_journal : Journal context root before inventory) (packet : Packet roles)
    (occurrence : Occurrence roles) : Prop :=
  occurrence = root ∨ occurrence = packet.site.occurrence ∨
    ∃ prior ∈ before.current.packets, prior.declaration.requirements ≠ [] ∧
      (occurrence = prior.site.occurrence ∨ ∃ clause ∈ prior.declaration.requirements,
        ∃ signature : clause.Signature roles, occurrence = clauseChild prior clause signature)

def childLabels (capture : Nat → Pattern) (clause : Clause) : List Pattern :=
  normalizeArgs (substArgs capture (normalizeArgs clause.arguments))

def HistoricalChildLabels (journal : Journal context root before inventory)
    (packet : Packet roles) (capture : Nat → Pattern) : Prop :=
  ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
    Protected journal packet (clauseChild packet clause signature) →
      journal.labels (clauseChild packet clause signature) = childLabels capture clause

def Assignment (packet : Packet roles) (capture : Nat → Pattern)
    (occurrence : Occurrence roles) (labels : List Pattern) : Prop :=
  ∃ clause ∈ packet.declaration.requirements, ∃ signature : clause.Signature roles,
    occurrence = clauseChild packet clause signature ∧ labels = childLabels capture clause

theorem assignment_unique (one : Assignment packet capture occurrence first)
    (two : Assignment packet capture occurrence last) : first = last := by
  obtain ⟨a,memberA,signatureA,atA,rfl⟩ := one
  obtain ⟨b,memberB,signatureB,atB,rfl⟩ := two
  rw [child_clause packet memberA memberB signatureA signatureB (atA.symm.trans atB)]

theorem extend (journal : Journal context root before inventory) (packet : Packet roles)
    (capture : Nat → Pattern) (compatible : HistoricalChildLabels journal packet capture) :
    ∃ labels : Occurrence roles → List Pattern,
      (∀ occurrence, Protected journal packet occurrence → labels occurrence = journal.labels occurrence) ∧
      ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
        labels (clauseChild packet clause signature) = childLabels capture clause := by
  classical
  let labels : Occurrence roles → List Pattern := fun occurrence =>
    if found : ∃ values, Assignment packet capture occurrence values then Classical.choose found else journal.labels occurrence
  have assigned (occurrence : Occurrence roles) (values : List Pattern)
      (known : Assignment packet capture occurrence values) : labels occurrence = values := by
    have found : ∃ values, Assignment packet capture occurrence values := ⟨values,known⟩
    simpa only [labels,dite_eq_left found] using assignment_unique (Classical.choose_spec found) known
  refine ⟨labels,?_,?_⟩
  · intro occurrence isProtected
    by_cases found : ∃ values, Assignment packet capture occurrence values
    · obtain ⟨values,clause,member,signature,located,rfl⟩ := found
      subst occurrence
      exact (assigned _ _ ⟨clause,member,signature,rfl,rfl⟩).trans (compatible clause member signature isProtected).symm
    · simp only [labels,dite_eq_right found]
  · intro clause member signature
    exact assigned _ _ ⟨clause,member,signature,rfl,rfl⟩

theorem new_packet (journal : Journal context root before inventory) (packet : Packet roles)
    (nonempty : packet.declaration.requirements ≠ [])
    (capture : Nat → Pattern) (trees : Nat → Expr Nat)
    (captureLabels : ∀ name, Label context (capture name) (trees name))
    (head : Aligned (fun pattern label => ∃ term, Label context label term ∧
      Matches (fun name part => Below (trees name) part)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
      (normalizeArgs packet.declaration.head) (journal.labels packet.site.occurrence))
    (compatible : HistoricalChildLabels journal packet capture) : NewPacket journal packet := by
  obtain ⟨labels,preserved,children⟩ := extend journal packet capture compatible
  have input := preserved packet.site.occurrence (Or.inr (Or.inl rfl))
  obtain ⟨clause,member⟩ := List.exists_mem_of_ne_nil _ nonempty
  refine ⟨labels,preserved root (Or.inl rfl),?_,?_⟩
  · intro prior member nonempty
    refine ⟨preserved prior.site.occurrence (Or.inr (Or.inr ⟨prior,member,nonempty,Or.inl rfl⟩)),?_⟩
    intro clause included signature
    exact preserved _ (Or.inr (Or.inr ⟨prior,member,nonempty,Or.inr ⟨clause,included,signature,rfl⟩⟩))
  · intro _
    exact ⟨{
      capture := capture
      trees := trees
      captureLabels := captureLabels
      coveredHead := (packet.checked.countsCovered clause member).1
      head := input.symm ▸ head
      children := children }⟩

theorem terminal_packet (journal : Journal context root before inventory) (packet : Packet roles)
    (empty : packet.declaration.requirements = []) : NewPacket journal packet :=
  ⟨journal.labels,rfl,fun _ _ _ => ⟨rfl,fun _ _ _ => rfl⟩,fun nonempty => False.elim (nonempty empty)⟩

end Yulang.GeneralNominalPacketChildLabels
