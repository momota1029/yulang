import Yulang.GeneralDictionaryFiniteJournalJoint

/-! A syntactic naming discipline for no-merge ordinary executions. Every
transition remains an actual guarded support update. The discipline constrains
only newly inserted occurrence IDs, not semantic branch validity or Joint.
Unrestricted execution is not proved to satisfy this discipline. -/
namespace Yulang.GeneralDictionaryNamedLocality
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

/-- The map fixes the whole occurrence associated with each identity. -/
def Named (names : Nat → Occurrence roles) (state : State roles) : Prop :=
  ∀ site ∈ state.sites, names site.occurrence.identity = site.occurrence

/-- The only additional checks concern occurrences newly inserted into sites.
There are no merge constructors: arbitrary identity aliasing is outside scope. -/
inductive At (names : Nat → Occurrence roles) (registry : Registry) (before : Tracked roles) :
    Occurrence roles → Tracked roles → Prop where
  | enqueue (focus : Occurrence roles)
      (linked : GeneralNominalState.Linked before.current.context.state focus.demand)
      (absent : ∀ site ∈ before.current.sites, site.occurrence ≠ focus)
      (named : names focus.identity = focus) :
      At names registry before focus {before with current := GeneralNominalSaturationState.enqueue before.current focus}
  | equate (focus : Occurrence roles) (first last : Nat)
      (one : first ∈ GeneralNominalState.sources before.current.context.state)
      (two : last ∈ GeneralNominalState.sources before.current.context.state)
      (equal : GeneralNominalFeedbackK2.Equal before.current first last)
      (novel : ¬ GeneralNominalFeedbackSteps.RawEqual before.current first last) :
      At names registry before focus {before with current := GeneralNominalFeedbackSteps.equate before.current first last}
  | install (packet : Packet roles) (support : List (Occurrence roles))
      (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
      (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current packet)
      (guard : PacketGuard before packet support)
      (named : ∀ child ∈ packet.children, names child.identity = child) :
      At names registry before packet.site.occurrence (GeneralNominalSupportSteps.install before packet support)

def Step (names : Nat → Occurrence roles) (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles) : Prop :=
  ∃ focus, Generated before.current root focus ∧ At names registry before focus after

theorem at_ordinary {names : Nat → Occurrence roles} {registry : Registry}
    {before after : Tracked roles} {focus : Occurrence roles}
    (action : At names registry before focus after) :
    GeneralDictionarySupportOrdinaryExecution.At registry before focus after := by
  cases action with
  | enqueue focus linked absent _ => exact .enqueue focus linked absent
  | equate focus first last one two equal novel => exact .equate focus first last one two equal novel
  | install packet support enabled novel guard _ => exact .install packet support enabled novel guard

theorem steps_ordinary {names : Nat → Occurrence roles} {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles}
    (path : B4Target.Steps (Step names registry root) before after) :
    B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior update ih =>
    obtain ⟨focus,generated,action⟩ := update
    exact .tail ih ⟨focus,generated,at_ordinary action⟩

theorem at_aliases {names : Nat → Occurrence roles} {registry : Registry}
    {before after : Tracked roles} {focus : Occurrence roles}
    (action : At names registry before focus after) : after.current.aliases = before.current.aliases := by
  cases action <;> rfl

theorem at_named {names : Nat → Occurrence roles} {registry : Registry}
    {before after : Tracked roles} {focus : Occurrence roles}
    (action : At names registry before focus after) (prior : Named names before.current) : Named names after.current := by
  intro site member
  cases action with
  | enqueue focus linked absent named =>
    rcases List.mem_append.mp member with old | added
    · exact prior site old
    · have same := List.mem_singleton.mp added
      subst site
      exact named
  | equate => exact prior site member
  | install packet support enabled novel guard named =>
    rcases List.mem_append.mp member with old | added
    · exact prior site old
    · obtain ⟨child,hchild,rfl⟩ := List.mem_map.mp added
      exact named child hchild

theorem initial_invariants (names : Nat → Occurrence roles) (registry : Registry)
    (root : Occurrence roles) (context : GeneralNominalCandidates.Context)
    (rootNamed : names root.identity = root) (state : Tracked roles)
    (path : B4Target.Steps (Step names registry root) (GeneralNominalSupport.initial context root) state) :
    Named names state.current ∧ state.current.aliases = [] := by
  induction path with
  | refl =>
    constructor
    · intro site member
      have same := List.mem_singleton.mp member
      subst site
      exact rootNamed
    · rfl
  | tail prior update ih =>
    obtain ⟨focus,generated,action⟩ := update
    exact ⟨at_named action ih.1,(at_aliases action).trans ih.2⟩

theorem alias_eq {state : State roles} (empty : state.aliases = [])
    {first last : Nat} (alias : Alias state first last) : first = last := by
  induction alias with
  | refl => rfl
  | edge member => rw [empty] at member; cases member
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

/-- Literal occurrence locality follows from an empty alias graph and the
syntactic names of sites and focus, without any model or selection premise. -/
theorem related_locality (names : Nat → Occurrence roles) (state : State roles)
    (named : Named names state) (empty : state.aliases = []) (focus : Occurrence roles)
    (focusNamed : names focus.identity = focus) (site : GeneralNominalDemandMerging.Site roles)
    (related : Related state focus site) : site.occurrence = focus := by
  have equal := alias_eq empty related.2
  exact (named site related.1).symm.trans ((congrArg names equal).symm.trans focusNamed)

/-- Actual finite named/no-merge histories discharge locality in the existing
finite-journal Joint theorem. Focus naming follows from its actual packet site. -/
theorem initial_joint (names : Nat → Occurrence roles) (registry : Registry)
    (root focus : Occurrence roles) (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (rootNamed : names root.identity = root) (state : Tracked roles)
    (path : B4Target.Steps (Step names registry root) (GeneralNominalSupport.initial context root) state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key := by
  have ordinary := steps_ordinary path
  have formed := GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) ordinary
  have inv := initial_invariants names registry root context rootNamed state path
  have focusNamed : names focus.identity = focus := by
    rw [← same]
    exact inv.1 packet.site (GeneralDictionaryFiniteJournalJoint.packet_site registry root state formed packet member)
  exact GeneralDictionaryFiniteJournalJoint.initial_joint registry root focus context source state ordinary
    packet member same key children selected (related_locality names state.current inv.1 inv.2 focus focusNamed) model valid
end Yulang.GeneralDictionaryNamedLocality
