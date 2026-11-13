import Yulang.GeneralNominalActualBudget

/-! Actual installation ancestry is reconstructed from the packet journal.
Finite instantiation labels give strict descent on every birth edge, even
when the occurrences are later aliased. -/
namespace Yulang.GeneralNominalPatersonLineage
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport

inductive Lineage (registry : Registry) (seed : Nat) (root : Occurrence roles)
    (packets : List (Packet roles)) : Nat → Occurrence roles → Prop
  | root : Lineage registry seed root packets 0 root
  | child (packet : Packet roles) : packet ∈ packets → packet.registry = registry →
      packet.context.state.seed = seed → packet.declaration ∈ registry.declarations →
      Lineage registry seed root packets depth packet.site.occurrence → child ∈ packet.children →
      Lineage registry seed root packets (depth+1) child

theorem lineage_mono (lineage : Lineage registry seed root first depth child) (included : first ⊆ last) :
    Lineage registry seed root last depth child := by
  induction lineage with
  | root => exact .root
  | child packet member sameRegistry sameSeed visible prior childMem ih =>
    exact .child packet (included member) sameRegistry sameSeed visible ih childMem

theorem lineage_ancestry (lineage : Lineage registry seed root packets depth child) :
    AtDepth registry seed root.identity depth child.identity := by
  induction lineage with
  | root => exact .root
  | child packet member sameRegistry sameSeed visible prior childMem ih =>
    have next := child_identity packet _ childMem (by simpa only [sameRegistry] using visible)
    rw [sameRegistry,sameSeed] at next
    exact .child ih next

theorem sites_lineage (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.current.sites,
      ∃ depth, Lineage registry context.state.seed root state.current.packets depth site.occurrence := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨0,.root⟩
  | @tail before after path step ih =>
    have formed := formed_trace (.initial context source) path
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered (formed_shared formed) generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact ih
    | merge => exact ih
    | install packet support enabled novel guard =>
      obtain ⟨depth,parent⟩ := ih packet.site enabled.1.2.2.1
      have seed : packet.context.state.seed = context.state.seed := by
        rw [enabled.1.2.1]; exact seed_trace path
      have included : before.current.packets ⊆ packet :: before.current.packets :=
        fun _ member => List.mem_cons_of_mem _ member
      intro site member
      change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨depth,prior⟩ := ih site old
        exact ⟨depth,lineage_mono prior included⟩
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        exact ⟨depth+1,.child packet (List.mem_cons_self ..) enabled.1.1 seed enabled.1.2.2.2.1
          (lineage_mono parent included) present⟩

theorem emitted_clause (packet : Packet roles) (child : Occurrence roles) (member : child ∈ packet.children) :
    ∃ clause ∈ packet.declaration.requirements, ∃ signature : clause.Signature roles,
      child = GeneralNominalFeedbackSites.clauseChild packet clause signature := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children at member
  obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
  have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
    packet.declaration packet.checked _ _).mem_iff.mpr present
  unfold GeneralDeclarationDemands.emitAll at old
  obtain ⟨clause,_,same⟩ := List.mem_map.mp old
  cases same
  exact ⟨clause.val,clause.property,_,rfl⟩

def mass (terms : List Pattern) : Nat := Roles.argsSize (counted terms)

/-- This is a finite syntax realization of the historical input equations.
It supplies neither descent inequalities nor an ancestry bound. Producing it
from actual shared-origin semantics is part of the source bridge. -/
structure Instantiation (labels : Occurrence roles → List Pattern) (packet : Packet roles) where
  capture : Nat → Pattern
  head : counted (labels packet.site.occurrence) = counted (substArgs capture packet.declaration.head)
  children : ∀ clause ∈ packet.declaration.requirements, ∀ signature : clause.Signature roles,
    counted (labels (GeneralNominalFeedbackSites.clauseChild packet clause signature)) =
      counted (substArgs capture clause.arguments)

theorem instantiated_child (realized : Instantiation labels packet) (member : child ∈ packet.children) :
    mass (labels child) < mass (labels packet.site.occurrence) := by
  obtain ⟨clause,present,signature,rfl⟩ := emitted_clause packet child member
  unfold mass
  rw [realized.children clause present signature,realized.head]
  exact (checked_child_descent packet.checked clause present realized.capture).1

theorem lineage_descent {roles : Roles.RoleDecls} {root child : Occurrence roles} {packets : List (Packet roles)} (lineage : Lineage registry seed root packets depth child)
    (labels : Occurrence roles → List Pattern)
    (realized : ∀ packet ∈ packets, Nonempty (Instantiation labels packet)) :
    depth + mass (labels child) ≤ mass (labels root) := by
  induction lineage with
  | root => exact Nat.zero_add _ ▸ Nat.le_refl _
  | child packet member sameRegistry sameSeed visible prior childMem ih =>
    obtain ⟨realization⟩ := realized packet member
    have strict := instantiated_child realization childMem
    omega

/-- One retrospective realization suffices for this complete finite journal;
alias transitions neither reset the birth depth nor remove its literal edges. -/
theorem reachable_depth (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (labels : Occurrence roles → List Pattern)
    (realized : ∀ packet ∈ state.current.packets, Nonempty (Instantiation labels packet))
    (site : GeneralNominalDemandMerging.Site roles) (member : site ∈ state.current.sites) :
    ∃ depth, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
      depth + mass (labels site.occurrence) ≤ mass (labels root) := by
  obtain ⟨depth,lineage⟩ := sites_lineage source path site member
  exact ⟨depth,lineage_ancestry lineage,lineage_descent lineage labels realized⟩

end Yulang.GeneralNominalPatersonLineage
