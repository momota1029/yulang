import Yulang.GeneralNominalActualInspectionSteps

/-! Actual emitted identities have a finite registry branching genealogy.
The open growth question is a uniform bound on its depth, not on steps. -/
namespace Yulang.GeneralNominalInvocationAncestry
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps

def successors (registry : Registry) (seed parent : Nat) : List Nat :=
  registry.declarations.flatMap fun declaration => declaration.requirements.map fun clause =>
    GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin parent declaration.id 6 clause.id 0)

inductive AtDepth (registry : Registry) (seed root : Nat) : Nat → Nat → Prop
  | root : AtDepth registry seed root 0 root
  | child : AtDepth registry seed root depth parent → identity ∈ successors registry seed parent →
      AtDepth registry seed root (depth+1) identity

def frontier (registry : Registry) (seed root : Nat) : Nat → List Nat
  | 0 => [root]
  | depth+1 => frontier registry seed root depth ++
      (frontier registry seed root depth).flatMap (successors registry seed)

theorem frontier_mono (small : first ≤ last) :
    frontier registry seed root first ⊆ frontier registry seed root last := by
  induction small with
  | refl => exact fun _ member => member
  | @step last small ih => exact fun _ member => List.mem_append_left _ (ih member)

theorem ancestry_enumerated (ancestry : AtDepth registry seed root depth identity) :
    identity ∈ frontier registry seed root depth := by
  induction ancestry with
  | root => exact List.mem_singleton_self _
  | child previous member ih =>
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨_,ih,member⟩)

theorem bounded_enumerated (ancestry : AtDepth registry seed root depth identity) (bounded : depth ≤ limit) :
    identity ∈ frontier registry seed root limit := frontier_mono bounded (ancestry_enumerated ancestry)

theorem child_identity (packet : Packet roles) (child : Occurrence roles) (member : child ∈ packet.children)
    (visible : packet.declaration ∈ packet.registry.declarations) :
    child.identity ∈ successors packet.registry packet.context.state.seed packet.site.occurrence.identity := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children at member
  obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
  have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
    packet.declaration packet.checked _ _).mem_iff.mpr present
  unfold GeneralDeclarationDemands.emitAll at old
  obtain ⟨clause,_,same⟩ := List.mem_map.mp old
  cases same
  exact List.mem_flatMap.mpr ⟨packet.declaration,visible,List.mem_map.mpr ⟨clause.val,clause.property,rfl⟩⟩

theorem seed_step (step : Step registry root before after) :
    after.current.context.state.seed = before.current.context.state.seed := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action =>
    cases action with
    | refresh _ certificate _ _ _ _ => exact certificate.refines.seed
    | enqueue | equate | reobserve => rfl
  | install packet support enabled novel guard =>
      change packet.context.state.seed = before.current.context.state.seed
      rw [enabled.1.2.1]
  | merge => rfl

theorem seed_trace (path : B4Target.Steps (Step registry root) before after) :
    after.current.context.state.seed = before.current.context.state.seed := by
  induction path with
  | refl => rfl
  | tail path step ih => exact (seed_step step).trans ih

theorem sites_ancestry (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.current.sites, ∃ depth, AtDepth registry context.state.seed root.identity depth site.occurrence.identity := by
  have formed : SourceFormed registry root (initial context root) := .initial context source
  induction path with
  | refl =>
      intro site member
      cases List.mem_singleton.mp member
      exact ⟨0,.root⟩
  | @tail before after path step ih =>
      have reached : ∀ {a b}, B4Target.Steps (Step registry root) a b →
          SourceFormed registry root a → SourceFormed registry root b := by
        intro a b trace
        induction trace with
        | refl => exact id
        | tail trace action inductionHypothesis => exact fun old => .update (inductionHypothesis old) action
      have current := reached path formed
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative focus after action =>
        cases action with
        | enqueue linked absent =>
            obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered
              (formed_shared current) generated
            exact False.elim (absent site member same)
        | refresh | equate | reobserve => exact ih
      | merge => exact ih
      | install packet support enabled novel guard =>
        intro site member
        change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
        rcases List.mem_append.mp member with old | new
        · exact ih site old
        · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp new
          obtain ⟨depth,ancestry⟩ := ih packet.site enabled.1.2.2.1
          refine ⟨depth+1,.child ancestry ?_⟩
          have next := child_identity packet child childMember (by simpa only [enabled.1.1] using enabled.1.2.2.2.1)
          have seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) enabled.1.2.1).trans
            (seed_trace path)
          simpa only [enabled.1.1,seed,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial,
            GeneralNominalSharedEmission.childSite] using next

/-- One residual growth obligation, phrased only in allocator ancestry.
It does not bound the number of installations or enumerate semantic deltas. -/
def InstalledDepthBound (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (limit : Nat) : Prop :=
  ∀ state, B4Target.Steps (Step registry root) (initial context root) state →
    ∀ packet : Packet roles, ∀ support,
      Generated state.current root packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.current packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.current packet → PacketGuard state packet support →
      ∃ depth, depth ≤ limit ∧ AtDepth registry context.state.seed root.identity depth packet.site.occurrence.identity

theorem installed_parents_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet)
    (guard : PacketGuard state packet support) :
    packet.site.occurrence.identity ∈ frontier registry context.state.seed root.identity limit := by
  obtain ⟨depth,small,ancestry⟩ := bound state path packet support generated enabled novel guard
  exact bounded_enumerated ancestry small

def allocationPool (registry : Registry) (seed : Nat) (parents : List Nat) : List Nat :=
  parents.flatMap fun parent => (GeneralNominalAllocation.keys registry parent).map
    (GeneralNominalIdentities.source seed)

theorem allocation_member (parent : Nat) (member : parent ∈ parents)
    (key : GeneralNominalIdentities.Origin) (allocated : key ∈ GeneralNominalAllocation.keys registry parent) :
    GeneralNominalIdentities.source seed key ∈ allocationPool registry seed parents :=
  List.mem_flatMap.mpr ⟨parent,member,List.mem_map.mpr ⟨key,allocated,rfl⟩⟩

theorem reservations_finite (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet)
    (guard : PacketGuard state packet support) :
    GeneralNominalAllocation.reserved packet.context.state packet.registry packet.site.occurrence.identity ⊆
      allocationPool registry context.state.seed (frontier registry context.state.seed root.identity limit) := by
  intro identity member
  obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
  have seed := (congrArg (fun c : GeneralNominalCandidates.Context => c.state.seed) enabled.1.2.1).trans (seed_trace path)
  simpa only [GeneralNominalAllocation.source,seed,enabled.1.1,GeneralNominalSupport.initial,
    GeneralNominalSaturationState.initial] using
    allocation_member (seed := context.state.seed) _ (installed_parents_finite bound path generated enabled novel guard)
      key (enabled.1.1 ▸ present)

end Yulang.GeneralNominalInvocationAncestry
