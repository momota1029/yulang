import Yulang.GeneralNominalPatternInventory
import Yulang.GeneralNominalBackedHoleElimination

/-! Source-key-preserving inventory transport and historical descent. Only
packets with children need a matching presentation; terminal declarations do
not acquire an extra coverage condition from this proof interface. -/
namespace Yulang.GeneralNominalCanonicalHoleJournal
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalHoleElimination
open GeneralNominalOpenPatternLabels GeneralNominalCanonicalPacketTransport GeneralNominalPatternInventory
open GeneralNominalPatersonLineage GeneralNominalActualInspectionSteps GeneralNominalSupport
open GeneralNominalSharedEnumeration

variable {roles : Roles.RoleDecls}

def History (context : GeneralNominalCandidates.Context) (labels : Occurrence roles → List Pattern)
    (packets : List (Packet roles)) : Prop :=
  ∀ packet ∈ packets, packet.declaration.requirements ≠ [] → Nonempty (Presentation context labels packet)

theorem history_transport (history : History context labels packets)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    History context (substituteLabels labels substitution) packets := by
  intro packet member nonempty
  obtain ⟨presented⟩ := history packet member nonempty
  exact ⟨GeneralNominalCanonicalPacketTransport.substitute presented substitution replacement images⟩

theorem history_descent (history : History context labels packets)
    (lineage : Lineage registry seed root packets depth child) :
    depth + mass (labels child) ≤ mass (labels root) := by
  induction lineage with
  | root => omega
  | child packet member sameRegistry sameSeed visible prior childMem ih =>
    obtain ⟨clause,present,signature,equal⟩ := emitted_clause packet _ childMem
    have nonempty : packet.declaration.requirements ≠ [] := by
      intro empty
      rw [empty] at present
      cases present
    obtain ⟨presented⟩ := history packet member nonempty
    have smaller := GeneralNominalPhaseLabels.child_descent (packetLabels presented) childMem
    omega

theorem history_parents (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (history : History context labels state.current.packets)
    (bounded : mass (labels root) ≤ limit) : GeneralNominalSnapshotCover.Parents registry context root limit state := by
  intro packet member
  obtain ⟨depth,lineage⟩ := GeneralNominalPhaseLabels.packets_lineage source path packet member
  have descent := history_descent history lineage
  exact GeneralNominalInvocationAncestry.bounded_enumerated (lineage_ancestry lineage) (by omega)

structure Journal (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (state : Tracked roles) (inventory : Inventory) where
  labels : Occurrence roles → List Pattern
  member : encodeList (labels root) ∈ inventory.terms
  rootLabels : ∀ pattern ∈ labels root, ∃ term, Label context pattern term
  history : History context labels state.current.packets

def patternReplacement (hole : Nat) (value : Pattern) (name : Nat) : Pattern :=
  if name = hole then value else .var name

theorem replacement_images (known : Label context value tree) :
    ∀ name, Label context (patternReplacement hole value name)
      (GeneralNominalHoleElimination.substitute hole tree name) := by
  intro name
  by_cases same : name = hole
  · simpa only [patternReplacement,GeneralNominalHoleElimination.substitute,same,ite_true] using known
  · simp only [patternReplacement,GeneralNominalHoleElimination.substitute,same,ite_false]
    exact ⟨rfl,by simp only [GeneralNominalInspection.translate,GeneralNominalCompoundReadback.quote],True.intro⟩

theorem encoded_images :
    (fun name => encode (patternReplacement hole value name)) =
      GeneralNominalHoleElimination.substitute hole (encode value) := by
  funext name
  by_cases same : name = hole <;>
    simp only [patternReplacement,GeneralNominalHoleElimination.substitute,same,ite_true,ite_false,encode]

theorem root_replacement (known : ∀ pattern ∈ patterns, ∃ term, Label context pattern term)
    (valueLabel : Label context value tree) :
    encodeList (normalizeArgs (substArgs (patternReplacement hole value) patterns)) =
      replace hole (encode value) (encodeList patterns) := by
  rw [substituted_root_code patterns known _ _ (replacement_images valueLabel),encoded_images]
  rfl

theorem filled_list (known : ∀ pattern ∈ patterns, ∃ term, Label context pattern term)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    ∀ pattern ∈ normalizeArgs (substArgs substitution patterns), ∃ term, Label context pattern term := by
  induction patterns with
  | nil => intro pattern impossible; cases impossible
  | cons head tail ih =>
    intro pattern member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨term,label⟩ := known head (List.mem_cons_self ..)
      exact ⟨_,filled_label label substitution replacement images⟩
    · exact ih (fun p member => known p (List.mem_cons_of_mem _ member)) pattern member

def Journal.replace (journal : Journal context root state inventory)
    (valueLabel : Label context value tree) (hole extra : Nat) :
    Journal context root state (eliminate inventory hole (encode value) extra) where
  labels := substituteLabels journal.labels (patternReplacement hole value)
  member := by
    change encodeList (normalizeArgs (substArgs (patternReplacement hole value) (journal.labels root))) ∈
      inventory.terms.map (GeneralNominalHoleElimination.replace hole (encode value))
    rw [root_replacement journal.rootLabels valueLabel]
    exact List.mem_map.mpr ⟨_,journal.member,rfl⟩
  rootLabels := filled_list journal.rootLabels _ _ (replacement_images valueLabel)
  history := history_transport journal.history _ _ (replacement_images valueLabel)

def Journal.retain (journal : Journal context root before inventory)
    (unchanged : after.current.packets ⊆ before.current.packets) : Journal context root after inventory where
  labels := journal.labels
  member := journal.member
  rootLabels := journal.rootLabels
  history := fun packet member => journal.history packet (unchanged member)

/-- Actual administrative actions and same-input merges keep the historical
presentation. No hypothesis about future depth or future growth is used. -/
def Journal.administrative (journal : Journal context root before inventory)
    (action : GeneralNominalSharedSteps.Administrative registry before.current focus after) :
    Journal context root {before with current := after} inventory := by
  apply journal.retain
  cases action <;> exact fun _ member => member

def Journal.install (journal : Journal context root before inventory)
    (packet : Packet roles) (support : List (Occurrence roles))
    (presented : packet.declaration.requirements ≠ [] → Nonempty (Presentation context journal.labels packet)) :
    Journal context root (GeneralNominalSharedSteps.install before packet support) inventory where
  labels := journal.labels
  member := journal.member
  rootLabels := journal.rootLabels
  history := by
    intro prior member nonempty
    rcases List.mem_cons.mp member with rfl | member
    · exact presented nonempty
    · exact journal.history prior member nonempty

theorem replacement_trace (inventory : Inventory) (present : hole ∈ inventory.holes)
    (closed : Closed (inventory.holes.erase hole) (encode value))
    (bounded : Bounded (inventory.holes.erase hole) tests extra (encode value)) :
    Trace tests (fun _ => extra) inventory (eliminate inventory hole (encode value) extra) 1 :=
  .next hole (encode value) present closed bounded (.refl _)

/-- The complete inventory and history part of an eliminating installation.
The new packet's simultaneous matching and the uniform semantic replacement
are source-production obligations, rather than numerical termination bounds. -/
theorem eliminating_install (journal : Journal context root before inventory)
    (valueLabel : Label context value tree) (present : hole ∈ inventory.holes)
    (closed : Closed (inventory.holes.erase hole) (encode value))
    (bounded : Bounded (inventory.holes.erase hole) tests extra (encode value))
    (packet : Packet roles) (support : List (Occurrence roles))
    (presented : packet.declaration.requirements ≠ [] → Nonempty (Presentation context
      (substituteLabels journal.labels (patternReplacement hole value)) packet)) :
    Trace tests (fun _ => extra) inventory (eliminate inventory hole (encode value) extra) 1 ∧
    Nonempty (Journal context root (GeneralNominalSharedSteps.install before packet support)
      (eliminate inventory hole (encode value) extra)) :=
  ⟨replacement_trace inventory present closed bounded,
    ⟨(journal.replace valueLabel hole extra).install packet support presented⟩⟩

def inventoryMass (inventory : Inventory) : Nat :=
  inventory.terms.foldr (fun term rest => max (mass (decodeList term)) rest) 0

theorem journal_bound (journal : Journal context root state inventory) :
    mass (journal.labels root) ≤ inventoryMass inventory := by
  have general (terms : List (Expr Nat)) (term : Expr Nat) (member : term ∈ terms) :
      mass (decodeList term) ≤ terms.foldr (fun term rest => max (mass (decodeList term)) rest) 0 := by
    induction terms with
    | nil => cases member
    | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih member) (Nat.le_max_right ..)
  simpa only [decode_encode_list,inventoryMass] using general inventory.terms _ journal.member

theorem journal_parents (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (journal : Journal context root state inventory) :
    GeneralNominalSnapshotCover.Parents registry context root (inventoryMass inventory) state :=
  history_parents source path journal.history (journal_bound journal)

end Yulang.GeneralNominalCanonicalHoleJournal
