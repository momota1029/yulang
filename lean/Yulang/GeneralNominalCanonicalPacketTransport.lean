import Yulang.GeneralNominalSubtermOrder

/-! Symbolic packet presentations survive every supported global
substitution. Historical mass bounds are recomputed from transformed matching;
capture trees are compared by a substitution-stable subterm relation. -/
namespace Yulang.GeneralNominalCanonicalPacketTransport
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalOriginTerms GeneralNominalHeadMatchMass GeneralNominalOpenPatternLabels
open GeneralNominalMatchedAssembly (Aligned)
open GeneralNominalPatersonLineage (mass)
open GeneralPatternNormalizedComposition GeneralNominalSubtermOrder

variable {roles : Roles.RoleDecls}

structure Presentation (context : GeneralNominalCandidates.Context)
    (labels : Occurrence roles → List Pattern) (packet : Packet roles) where
  capture : Nat → Pattern
  trees : Nat → Expr Nat
  captureLabels : ∀ name, Label context (capture name) (trees name)
  coveredHead : coveredArgs (normalizeArgs packet.declaration.head) = true
  head : Aligned (fun pattern label => ∃ term, Label context label term ∧
    Matches (fun name part => Below (trees name) part)
      (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
    (normalizeArgs packet.declaration.head) (labels packet.site.occurrence)
  children : ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
    labels (GeneralNominalFeedbackSites.clauseChild packet clause signature) =
      normalizeArgs (substArgs capture (normalizeArgs clause.arguments))

def substituteLabels (labels : Occurrence roles → List Pattern) (substitution : Nat → Pattern) :
    Occurrence roles → List Pattern := fun occurrence => normalizeArgs (substArgs substitution (labels occurrence))

theorem matches_bind {capture : Nat → Expr Nat} (matched : Matches (fun name part => Below (capture name) part) query term)
    (substitution : Nat → Expr Nat) :
    Matches (fun name part => Below ((capture name).bind substitution) part) query (term.bind substitution) := by
  induction matched with
  | capture same => exact .capture (below_bind same substitution)
  | scalar children => exact .scalar _
  | structural shape queries children matched ih => exact .structural shape queries _ ih
  | nominal name count queries children matched ih => exact .nominal name count queries _ ih

/-- Recompute the checker mass from the retained presentation, with exact
multiplicity for every replaced leaf. -/
theorem filled_mass_exact (known : Label context pattern term)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    mass [normalize (pattern.subst substitution)] =
      weightedTree (fun name => weight (replacement name)) term := by
  rw [label_mass (filled_label known substitution replacement images)]
  exact weighted_bind term replacement (fun _ => 1)

theorem head_substitute {capture : Nat → Expr Nat}
    (head : Aligned (fun pattern label => ∃ term, Label context label term ∧
      Matches (fun name part => Below (capture name) part)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term) patterns labels)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    Aligned (fun pattern label => ∃ term, Label context label term ∧
      Matches (fun name part => Below ((capture name).bind replacement) part)
        (GeneralNominalInspection.translate context.state.constructors context.interpretation pattern) term)
      patterns (normalizeArgs (substArgs substitution labels)) := by
  induction head with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨term,label,matched⟩ := first
    exact .cons ⟨term.bind replacement,filled_label label substitution replacement images,matches_bind matched replacement⟩ ih

def substitute (presented : Presentation context labels packet)
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    Presentation context (substituteLabels labels substitution) packet where
  capture := compose presented.capture substitution
  trees := fun name => (presented.trees name).bind replacement
  captureLabels := fun name => filled_label (presented.captureLabels name) substitution replacement images
  coveredHead := presented.coveredHead
  head := head_substitute presented.head substitution replacement images
  children := by
    intro clause member signature
    unfold substituteLabels
    rw [presented.children clause member signature]
    exact normalized_args_compose _ (packet.checked.countsCovered clause member).2 _ _
      (fun name => (presented.captureLabels name).1) (fun name => (images name).1)

theorem head_mass (presented : Presentation context labels packet) :
    mass (substArgs presented.capture (normalizeArgs packet.declaration.head)) ≤ mass (labels packet.site.occurrence) := by
  apply GeneralNominalOpenChildProduction.list_mass presented.head presented.coveredHead presented.capture
  intro name term same
  have smaller := mass_below same
  have exactMass := label_mass (presented.captureLabels name)
  simpa only [mass,counted,normalizeArgs,encodeArgs,Roles.argsSize,Nat.add_zero] using Nat.le_trans (Nat.le_of_eq exactMass) smaller

def packetLabels (presented : Presentation context labels packet) : GeneralNominalPhaseLabels.PacketLabels labels packet where
  capture := presented.capture
  head := head_mass presented
  children := by
    intro clause member signature
    rw [presented.children clause member signature]
    unfold counted
    exact congrArg encodeArgs (normal_args_idempotent _
      (GeneralNominalTemplateSubstitution.args_subst_covered _ (packet.checked.countsCovered clause member).2 _
        (fun name => (presented.captureLabels name).1)))

/-- Every historical packet is transported with the same source substitution.
Different nominal source keys remain in the exact child-label equations. -/
theorem history_substitute {packets : List (Packet roles)} (history : ∀ packet ∈ packets, Nonempty (Presentation context labels packet))
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    ∀ packet ∈ packets, Nonempty (Presentation context (substituteLabels labels substitution) packet) := by
  intro packet member
  obtain ⟨presented⟩ := history packet member
  exact ⟨substitute presented substitution replacement images⟩

theorem transported_packet_labels {packets : List (Packet roles)} (history : ∀ packet ∈ packets, Nonempty (Presentation context labels packet))
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    ∀ packet ∈ packets, Nonempty (GeneralNominalPhaseLabels.PacketLabels (substituteLabels labels substitution) packet) := by
  intro packet member
  obtain ⟨presented⟩ := history_substitute history substitution replacement images packet member
  exact ⟨packetLabels presented⟩

/-- The transformed actual journal gives the usual snapshot ancestry bound;
this result has no numerical bound on the substituted source holes. -/
theorem parents_after_substitution
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (history : ∀ packet ∈ state.current.packets, Nonempty (Presentation context labels packet))
    (substitution : Nat → Pattern) (replacement : Nat → Expr Nat)
    (images : ∀ name, Label context (substitution name) (replacement name)) :
    GeneralNominalSnapshotCover.Parents registry context root
      (mass (substituteLabels labels substitution root)) state :=
  GeneralNominalPhaseLabels.parents source path _
    (transported_packet_labels history substitution replacement images) (Nat.le_refl _)

end Yulang.GeneralNominalCanonicalPacketTransport
