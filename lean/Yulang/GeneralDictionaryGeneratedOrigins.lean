import Yulang.GeneralDictionaryReachableRootIntervals

/-! Actual generated demands cannot appear without the original root or a
recorded packet emission. This tracks complete occurrences, not just IDs. -/
namespace Yulang.GeneralDictionaryGeneratedOrigins
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
variable {roles : Roles.RoleDecls}

def Origin (state : State roles) (root child : Occurrence roles) : Prop :=
  child = root ∨ ∃ packet ∈ state.packets, child ∈ packet.children

def Recorded (state : State roles) (root : Occurrence roles) : Prop :=
  (∀ site ∈ state.sites, Origin state root site.occurrence) ∧
  (∀ first child, (first,child) ∈ state.edges → Origin state root child)

theorem generated (state : State roles) (root child : Occurrence roles)
    (recorded : Recorded state root) (reached : Generated state root child) : Origin state root child := by
  induction reached with
  | root => exact Or.inl rfl
  | child _ member _ => exact recorded.2 _ _ member
  | alias _ _ member _ _ => exact recorded.1 _ member

theorem monotone {before after : State roles} {root child : Occurrence roles}
    (packets : ∀ packet ∈ before.packets, packet ∈ after.packets)
    (origin : Origin before root child) : Origin after root child := by
  rcases origin with same | ⟨packet,member,emitted⟩
  · exact Or.inl same
  · exact Or.inr ⟨packet,packets packet member,emitted⟩

theorem administrative {registry : Registry} {before after : State roles} {root focus : Occurrence roles}
    (recorded : Recorded before root) (origin : Origin before root focus)
    (action : GeneralNominalSupportSteps.Administrative registry before focus after) : Recorded after root := by
  cases action with
  | enqueue linked absent =>
    refine ⟨?_,recorded.2⟩
    intro site member
    rcases List.mem_append.mp member with old | added
    · exact recorded.1 site old
    · have equal := List.mem_singleton.mp added
      subst site
      exact origin
  | refresh => exact recorded
  | equate => exact recorded
  | reobserve => exact recorded

theorem installed (before : State roles) (root : Occurrence roles) (packet : Packet roles)
    (recorded : Recorded before root) :
    Recorded (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) root := by
  have old {child : Occurrence roles} (source : Origin before root child) :
      Origin (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) root child :=
    monotone (fun _ member => List.mem_cons_of_mem _ member) source
  constructor
  · intro site member
    rcases List.mem_append.mp member with prior | emitted
    · exact old (recorded.1 site prior)
    · obtain ⟨child,childMember,same⟩ := List.mem_map.mp emitted
      subst site
      exact Or.inr ⟨packet,List.mem_cons_self,childMember⟩
  · intro first child member
    rcases List.mem_append.mp member with prior | emitted
    · exact old (recorded.2 first child prior)
    · obtain ⟨actual,member,equal⟩ := List.mem_map.mp emitted
      have same := congrArg Prod.snd equal
      change actual = child at same
      subst actual
      exact Or.inr ⟨packet,List.mem_cons_self,member⟩

theorem step {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (recorded : Recorded before.current root)
    (action : GeneralNominalValueSteps.Step registry root before after) : Recorded after.current root := by
  obtain ⟨focus,reached,action⟩ := action
  cases action with
  | administrative _ _ action => exact administrative recorded (generated _ _ _ recorded reached) action
  | install packet support enabled novel guard => exact installed before.current root packet recorded
  | merge => exact recorded

theorem reachable {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state) :
    Recorded state.current root := by
  obtain ⟨start,initial,path⟩ := reachable
  induction path with
  | refl =>
    obtain ⟨context,source,rfl⟩ := initial
    constructor
    · intro site member
      have same := List.mem_singleton.mp member
      subst site
      exact Or.inl rfl
    · intro first child member
      cases member
  | tail _ action ih => exact step ih action

theorem reachable_generated {registry : Registry} {root child : Occurrence roles} {state : Tracked roles}
    (path : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (reached : Generated state.current root child) : Origin state.current root child :=
  generated _ _ _ (reachable path) reached

end Yulang.GeneralDictionaryGeneratedOrigins
