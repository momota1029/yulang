import Yulang.GeneralNominalPacketChildLabels

/-! Historical matching is indexed by invocation identity. A repeated
invocation can retain its presentation even when its endpoint demand changes.
Fresh child identities extend the same label function without collisions. -/
namespace Yulang.GeneralNominalIdentityJournal
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalHoleElimination
open GeneralNominalCanonicalHoleJournal GeneralNominalCanonicalPacketTransport
open GeneralNominalPatersonLineage GeneralNominalInvocationAncestry
open GeneralNominalFeedbackSites GeneralNominalPacketChildLabels
open GeneralNominalSourceProducerHandoff GeneralNominalMatchedAssembly
open GeneralNominalOriginTerms GeneralNominalOpenPatternLabels GeneralNominalHeadMatchMass
open GeneralNominalSubtermOrder GeneralNominalCompatibleJournalExtension

variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : Tracked roles}

def IdentityLabels (labels : Occurrence roles → List Pattern) : Prop :=
  ∀ first last, first.identity = last.identity → labels first = labels last

theorem identity_substitute (known : IdentityLabels labels) (replacement : Nat → Pattern) :
    IdentityLabels (substituteLabels labels replacement) := by
  intro first last same
  unfold substituteLabels
  rw [known first last same]

theorem child_identity (packet : Packet roles) (clause : Clause) (signature : clause.Signature roles) :
    (clauseChild packet clause signature).identity = GeneralNominalIdentities.source packet.context.state.seed
      (GeneralNominalAllocation.origin packet.site.occurrence.identity packet.declaration.id 6 clause.id 0) := rfl

theorem child_parent (packet : Packet roles) (clause : Clause) (signature : clause.Signature roles) :
    packet.site.occurrence.identity < (clauseChild packet clause signature).identity := by
  rw [child_identity]
  exact GeneralNominalIdentities.source_above_invocation packet.context.state.seed
    (GeneralNominalAllocation.origin packet.site.occurrence.identity packet.declaration.id 6 clause.id 0)

theorem child_same (first last : Packet roles)
    (seed : first.context.state.seed = last.context.state.seed)
    (parent : first.site.occurrence.identity = last.site.occurrence.identity)
    (declaration : first.declaration = last.declaration)
    (clause : Clause) (signature : clause.Signature roles) :
    (clauseChild first clause signature).identity = (clauseChild last clause signature).identity := by
  rw [child_identity,child_identity,seed,parent,declaration]

def presentation (known : IdentityLabels labels) (prior : Presentation context labels first)
    (seed : first.context.state.seed = last.context.state.seed)
    (parent : first.site.occurrence.identity = last.site.occurrence.identity)
    (declaration : first.declaration = last.declaration) : Presentation context labels last where
  capture := prior.capture
  trees := prior.trees
  captureLabels := prior.captureLabels
  coveredHead := declaration ▸ prior.coveredHead
  head := by
    rw [← declaration,← known _ _ parent]
    exact prior.head
  children := by
    intro clause member signature
    rw [← known _ _ (child_same first last seed parent declaration clause signature)]
    exact prior.children clause (declaration ▸ member) signature

theorem lineage_above (lineage : Lineage registry seed root packets depth occurrence) :
    root.identity ≤ occurrence.identity := by
  induction lineage with
  | root => exact Nat.le_refl _
  | child packet member registry seed visible parent childMem ih =>
    obtain ⟨clause,present,signature,rfl⟩ := emitted_clause packet _ childMem
    exact Nat.le_trans ih (Nat.le_of_lt (child_parent packet clause signature))

theorem child_collision (checked : Checked registry) (first last : Packet roles)
    (firstVisible : first.declaration ∈ registry.declarations)
    (lastVisible : last.declaration ∈ registry.declarations)
    (seed : first.context.state.seed = last.context.state.seed)
    (a b : Clause) (one : a.Signature roles) (two : b.Signature roles)
    (same : (clauseChild first a one).identity = (clauseChild last b two).identity) :
    first.site.occurrence.identity = last.site.occurrence.identity ∧ first.declaration = last.declaration := by
  rw [child_identity,child_identity,seed] at same
  have tuple := (GeneralNominalIdentities.source_identity _ _ _).mp same
  exact ⟨congrArg Prod.fst tuple,identified checked.1 firstVisible lastVisible (congrArg (fun key => key.2.1) tuple)⟩

theorem child_clause_id (packet : Packet roles)
    (one : a ∈ packet.declaration.requirements) (two : b ∈ packet.declaration.requirements)
    (first : a.Signature roles) (last : b.Signature roles)
    (same : (clauseChild packet a first).identity = (clauseChild packet b last).identity) : a = b := by
  rw [child_identity,child_identity] at same
  have tuple := (GeneralNominalIdentities.source_identity _ _ _).mp same
  exact identified packet.checked.identified.1 one two (congrArg (fun key => key.2.2.2.1) tuple)

def Used (root : Occurrence roles) (packets : List (Packet roles)) (identity : Nat) : Prop :=
  identity = root.identity ∨ ∃ prior ∈ packets,
    identity = prior.site.occurrence.identity ∨ ∃ clause ∈ prior.declaration.requirements,
      ∃ signature : clause.Signature roles, identity = (clauseChild prior clause signature).identity

theorem fresh_children (checked : Checked registry)
    (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (parent : ∃ depth, Lineage registry seed root packets depth packet.site.occurrence)
    (configuration : ∀ prior ∈ packets, prior.context.state.seed = packet.context.state.seed ∧
      prior.declaration ∈ registry.declarations ∧
      ∃ depth, Lineage registry seed root packets depth prior.site.occurrence)
    (fresh : ∀ prior ∈ packets, ¬ (prior.site.occurrence.identity = packet.site.occurrence.identity ∧
      prior.declaration = packet.declaration))
    (clause : Clause) (signature : clause.Signature roles) :
    ¬ Used root packets (clauseChild packet clause signature).identity := by
  have above : root.identity < (clauseChild packet clause signature).identity :=
    Nat.lt_of_le_of_lt (lineage_above parent.choose_spec) (child_parent packet clause signature)
  rintro (same | ⟨prior,member,same | ⟨other,included,valid,same⟩⟩)
  · exact Nat.ne_of_lt above same.symm
  · obtain ⟨depth,lineage⟩ := (configuration prior member).2.2
    cases lineage with
    | root => exact Nat.ne_of_lt above same.symm
    | child producer recorded reg source shown ancestry childMem =>
      obtain ⟨other,included,valid,atChild⟩ := emitted_clause producer _ childMem
      rw [atChild] at same
      have collision := child_collision checked packet producer visible (configuration producer recorded).2.1
        (configuration producer recorded).1.symm clause other signature valid same
      exact fresh producer recorded ⟨collision.1.symm,collision.2.symm⟩
  · have collision := child_collision checked packet prior visible (configuration prior member).2.1
      (configuration prior member).1.symm clause other signature valid same
    exact fresh prior member ⟨collision.1.symm,collision.2.symm⟩

def ChildAssignment (packet : Packet roles) (capture : Nat → Pattern) (identity : Nat) (labels : List Pattern) : Prop :=
  ∃ clause ∈ packet.declaration.requirements, ∃ signature : clause.Signature roles,
    identity = (clauseChild packet clause signature).identity ∧ labels = childLabels capture clause

theorem assignment_unique (one : ChildAssignment packet capture identity first)
    (two : ChildAssignment packet capture identity last) : first = last := by
  obtain ⟨a,memberA,signatureA,atA,rfl⟩ := one
  obtain ⟨b,memberB,signatureB,atB,rfl⟩ := two
  rw [child_clause_id packet memberA memberB signatureA signatureB (atA.symm.trans atB)]

theorem extend (journal : Journal context root state inventory) (packet : Packet roles)
    (identity : IdentityLabels journal.labels) (capture : Nat → Pattern)
    (fresh : ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
      ¬ Used root state.current.packets (clauseChild packet clause signature).identity) :
    ∃ labels : Occurrence roles → List Pattern, IdentityLabels labels ∧
      (∀ occurrence, Used root state.current.packets occurrence.identity → labels occurrence = journal.labels occurrence) ∧
      labels packet.site.occurrence = journal.labels packet.site.occurrence ∧
      ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
        labels (clauseChild packet clause signature) = childLabels capture clause := by
  classical
  let labels : Occurrence roles → List Pattern := fun occurrence =>
    if found : ∃ values, ChildAssignment packet capture occurrence.identity values then Classical.choose found else journal.labels occurrence
  have assigned (occurrence : Occurrence roles) (values : List Pattern)
      (known : ChildAssignment packet capture occurrence.identity values) : labels occurrence = values := by
    have found : ∃ values, ChildAssignment packet capture occurrence.identity values := ⟨values,known⟩
    simpa only [labels,dite_eq_left found] using assignment_unique (Classical.choose_spec found) known
  refine ⟨labels,?_,?_,?_,?_⟩
  · intro first last same
    dsimp only [labels]
    rw [same,identity first last same]
  · intro occurrence used
    have absent : ¬ ∃ values, ChildAssignment packet capture occurrence.identity values := by
      rintro ⟨values,clause,member,signature,same,_⟩
      exact fresh clause member signature (same ▸ used)
    simp only [labels,dite_eq_right absent]
  · have absent : ¬ ∃ values, ChildAssignment packet capture packet.site.occurrence.identity values := by
      rintro ⟨values,clause,member,signature,same,_⟩
      exact Nat.ne_of_lt (child_parent packet clause signature) same
    simp only [labels,dite_eq_right absent]
  · intro clause member signature
    exact assigned _ _ ⟨clause,member,signature,rfl,rfl⟩

def Matching (context : GeneralNominalCandidates.Context)
    (labels : Occurrence roles → List Pattern) (packet : Packet roles) : Prop :=
  ∃ capture : Nat → Pattern, ∃ trees : Nat → Expr Nat,
    (∀ name, Label context (capture name) (trees name)) ∧
    Aligned (fun pattern label => ∃ term, Label context label term ∧
      Matches (fun name part => Below (trees name) part)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
      (normalizeArgs packet.declaration.head) (labels packet.site.occurrence)

theorem new_packet_extension_preserving (checked : Checked registry)
    (journal : Journal context root state inventory) (identity : IdentityLabels journal.labels)
    (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (parent : ∃ depth, Lineage registry seed root state.current.packets depth packet.site.occurrence)
    (configuration : ∀ prior ∈ state.current.packets, prior.context.state.seed = packet.context.state.seed ∧
      prior.declaration ∈ registry.declarations ∧
      ∃ depth, Lineage registry seed root state.current.packets depth prior.site.occurrence)
    (matching : packet.declaration.requirements ≠ [] → Matching context journal.labels packet) :
    ∃ labels, IdentityLabels labels ∧
      (∀ occurrence, Used root state.current.packets occurrence.identity → labels occurrence = journal.labels occurrence) ∧
      labels root = journal.labels root ∧
      (∀ prior ∈ state.current.packets, prior.declaration.requirements ≠ [] → Agrees journal.labels labels prior) ∧
      (packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet)) := by
  classical
  by_cases terminal : packet.declaration.requirements = []
  · exact ⟨journal.labels,identity,(fun _ _ => rfl),rfl,fun _ _ _ => ⟨rfl,fun _ _ _ => rfl⟩,
      fun nonempty => False.elim (nonempty terminal)⟩
  by_cases repeated : ∃ prior ∈ state.current.packets,
      prior.site.occurrence.identity = packet.site.occurrence.identity ∧ prior.declaration = packet.declaration
  · obtain ⟨prior,member,same,decl⟩ := repeated
    obtain ⟨old⟩ := journal.history prior member (by simpa only [decl] using terminal)
    exact ⟨journal.labels,identity,(fun _ _ => rfl),rfl,fun _ _ _ => ⟨rfl,fun _ _ _ => rfl⟩,
      fun _ => ⟨presentation identity old (configuration prior member).1 same decl⟩⟩
  · have fresh : ∀ prior ∈ state.current.packets,
        ¬ (prior.site.occurrence.identity = packet.site.occurrence.identity ∧ prior.declaration = packet.declaration) :=
      fun prior member same => repeated ⟨prior,member,same⟩
    obtain ⟨capture,trees,captureLabels,head⟩ := matching terminal
    obtain ⟨labels,newIdentity,preserved,input,children⟩ := extend journal packet identity capture
      (fun clause _ signature => fresh_children checked packet visible parent configuration fresh clause signature)
    obtain ⟨clause,member⟩ := List.exists_mem_of_ne_nil _ terminal
    refine ⟨labels,newIdentity,preserved,preserved root (Or.inl rfl),?_,?_⟩
    · intro prior present _
      refine ⟨preserved _ (Or.inr ⟨prior,present,Or.inl rfl⟩),?_⟩
      intro clause included signature
      exact preserved _ (Or.inr ⟨prior,present,Or.inr ⟨clause,included,signature,rfl⟩⟩)
    · intro _
      exact ⟨{
        capture := capture
        trees := trees
        captureLabels := captureLabels
        coveredHead := (packet.checked.countsCovered clause member).1
        head := input.symm ▸ head
        children := children }⟩

theorem new_packet_extension (checked : Checked registry)
    (journal : Journal context root state inventory) (identity : IdentityLabels journal.labels)
    (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (parent : ∃ depth, Lineage registry seed root state.current.packets depth packet.site.occurrence)
    (configuration : ∀ prior ∈ state.current.packets, prior.context.state.seed = packet.context.state.seed ∧
      prior.declaration ∈ registry.declarations ∧
      ∃ depth, Lineage registry seed root state.current.packets depth prior.site.occurrence)
    (matching : packet.declaration.requirements ≠ [] → Matching context journal.labels packet) :
    ∃ labels, IdentityLabels labels ∧ labels root = journal.labels root ∧
      (∀ prior ∈ state.current.packets, prior.declaration.requirements ≠ [] → Agrees journal.labels labels prior) ∧
      (packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet)) := by
  obtain ⟨labels,indexed,preserved,same,history,presented⟩ := new_packet_extension_preserving checked journal
    identity packet visible parent configuration matching
  exact ⟨labels,indexed,same,history,presented⟩

theorem packet_configuration
    (path : B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (GeneralNominalSupport.initial context root) state) :
    ∀ packet ∈ state.current.packets,
      packet.context.state.seed = context.state.seed ∧ packet.declaration ∈ registry.declarations := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | merge => exact ih
    | install packet support enabled novel guard =>
      intro prior member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨(congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.seed) enabled.1.2.1).trans
          (GeneralNominalActualTraceSupport.configuration_trace path).1,enabled.1.2.2.2.1⟩
      · exact ih prior member

theorem reachable_new_packet (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (journal : Journal context root state inventory) (identity : IdentityLabels journal.labels)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (matching : packet.declaration.requirements ≠ [] → Matching context journal.labels packet) : NewPacket journal packet := by
  have seed : packet.context.state.seed = context.state.seed := by
    rw [enabled.1.2.1]
    exact (GeneralNominalActualTraceSupport.configuration_trace path).1
  obtain ⟨labels,_,rootSame,history,presented⟩ := new_packet_extension checked journal identity packet enabled.1.2.2.2.1
    (sites_lineage source path packet.site enabled.1.2.2.1)
    (fun prior member => ⟨(packet_configuration path prior member).1.trans seed.symm,
      (packet_configuration path prior member).2,GeneralNominalPhaseLabels.packets_lineage source path prior member⟩)
    matching
  exact ⟨labels,rootSame,history,presented⟩

end Yulang.GeneralNominalIdentityJournal
