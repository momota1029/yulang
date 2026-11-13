import Yulang.GeneralNominalSnapshotCover
import Yulang.GeneralNominalGroundHeadMatching

/-! Normalized symbolic journal labels. A single snapshot realization gives
its own finite cover; it need not bound labels at subsequent refinements. -/
namespace Yulang.GeneralNominalPhaseLabels
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalPatersonLineage GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport

variable {roles : Roles.RoleDecls}

structure PacketLabels (labels : Occurrence roles → List Pattern) (packet : Packet roles) where
  capture : Nat → Pattern
  head : mass (substArgs capture (normalizeArgs packet.declaration.head)) ≤ mass (labels packet.site.occurrence)
  children : ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
    counted (labels (GeneralNominalFeedbackSites.clauseChild packet clause signature)) =
      counted (substArgs capture (normalizeArgs clause.arguments))

theorem child_descent (matched : PacketLabels labels packet) (member : child ∈ packet.children) :
    mass (labels child) < mass (labels packet.site.occurrence) := by
  obtain ⟨clause,present,signature,rfl⟩ := emitted_clause packet child member
  have strict := GeneralPatternConservativeSubstitution.checked_normalized_descent packet.checked clause present matched.capture
  change mass (substArgs matched.capture (normalizeArgs clause.arguments)) <
    mass (substArgs matched.capture (normalizeArgs packet.declaration.head)) at strict
  have equal : mass (labels (GeneralNominalFeedbackSites.clauseChild packet clause signature)) =
      mass (substArgs matched.capture (normalizeArgs clause.arguments)) := congrArg Roles.argsSize (matched.children clause present signature)
  have head := matched.head
  omega

theorem lineage_descent {root child : Occurrence roles} {packets : List (Packet roles)}
    (lineage : Lineage registry seed root packets depth child)
    (labels : Occurrence roles → List Pattern)
    (realized : ∀ packet ∈ packets, Nonempty (PacketLabels labels packet)) :
    depth + mass (labels child) ≤ mass (labels root) := by
  induction lineage with
  | root => omega
  | child packet member sameRegistry sameSeed visible prior childMem ih =>
    obtain ⟨matched⟩ := realized packet member
    have strict := child_descent matched childMem
    omega

theorem packets_lineage (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.current.packets,
      ∃ depth, Lineage registry context.state.seed root state.current.packets depth packet.site.occurrence := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | merge => exact ih
    | install packet support enabled novel guard =>
      intro prior member
      have included : before.current.packets ⊆ packet :: before.current.packets := fun _ h => List.mem_cons_of_mem _ h
      rcases List.mem_cons.mp member with rfl | old
      · obtain ⟨depth,lineage⟩ := sites_lineage source path prior.site enabled.1.2.2.1
        exact ⟨depth,lineage_mono lineage included⟩
      · obtain ⟨depth,lineage⟩ := ih prior old
        exact ⟨depth,lineage_mono lineage included⟩

theorem parents (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (labels : Occurrence roles → List Pattern)
    (realized : ∀ packet ∈ state.current.packets, Nonempty (PacketLabels labels packet))
    (bounded : mass (labels root) ≤ limit) : GeneralNominalSnapshotCover.Parents registry context root limit state := by
  intro packet member
  obtain ⟨depth,lineage⟩ := packets_lineage source path packet member
  have smaller := lineage_descent lineage labels realized
  exact GeneralNominalInvocationAncestry.bounded_enumerated (lineage_ancestry lineage) (by omega)

/-- The closed per-phase engine is unconditional. Its semantic Inputs premise
is local to this packet and model, with no universal GroundRoots premise. -/
theorem closed_packet_descent {root : Occurrence roles} {packet : Packet roles}
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (guard : PacketGuard state packet support) (nonempty : packet.declaration.requirements ≠ [])
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) (branch : packet.Holds model)
    (known : GeneralNominalGroundAccessibility.Inputs context model packet.site labels) :
    ∀ child ∈ packet.children, ∃ childLabels,
      GeneralNominalGroundAccessibility.Inputs context model (GeneralNominalSharedEmission.childSite packet child) childLabels ∧
        mass childLabels < mass labels := by
  have production := GeneralNominalNormalizedGround.packet_production
    (GeneralNominalCaptureAssembly.factorization_of_assembly
      (GeneralNominalGroundHeadMatching.normalized_capture_assembly (roles := roles) (registry := registry) (context := context) (root := root)))
  have config := configuration_trace path
  obtain ⟨capture,head,children⟩ := production state packet support path config.2.1 config.2.2
    enabled guard nonempty model valid branch labels known
  intro child member
  obtain ⟨clause,present,signature,rfl⟩ := emitted_clause packet child member
  refine ⟨_,children clause present signature,?_⟩
  have strict := GeneralPatternConservativeSubstitution.checked_normalized_descent packet.checked clause present capture
  change mass (substArgs capture (normalizeArgs clause.arguments)) < mass (substArgs capture (normalizeArgs packet.declaration.head)) at strict
  omega

end Yulang.GeneralNominalPhaseLabels
