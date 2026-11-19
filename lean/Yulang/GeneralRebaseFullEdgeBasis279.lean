import Yulang.GeneralRebaseClosedChildIdentity279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseFullEdgeBasis279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseClosedChildShape279 (ClosedArguments)
open GeneralRebaseClosedChildIdentity279 (cross_trace)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralRebaseSourceEdgeBasis279 (project finite_projected_edges initial_edges)
open GeneralNominalCenteredHeadAllocEncoding (registry)

def Registered (state : State roles) (focus : Occurrence roles) : Prop :=
  ∃ raw ∈ state.core.erased.current.sites, raw.occurrence = focus

theorem endpoints {r : Registry} {root : Occurrence roles} {start state : State roles}
    (source : (boundary roles).Initial r root start)
    (walk : B4Target.Steps ((boundary roles).Step r root) start state) :
    ∀ e ∈ state.core.erased.current.edges, Registered state e.1 ∧ Registered state e.2 := by
  induction walk with
  | refl =>
    intro e member
    rw [initial_edges source] at member
    cases member
  | @tail mid final _ actual ih =>
    obtain ⟨focus,_,action⟩ := actual
    have lift {occ : Occurrence roles} (old : Registered mid occ) : Registered final occ := by
      obtain ⟨raw,mem,same⟩ := old
      exact ⟨raw,(GeneralNominalVersionedMixedGrowth234.at_growth action).legacy.rawSites mem,same⟩
    cases action with
    | administrative admin =>
      cases admin <;> intro e member <;> exact ⟨lift (ih e member).1,lift (ih e member).2⟩
    | refresh | merge =>
      intro e member
      exact ⟨lift (ih e member).1,lift (ih e member).2⟩
    | install eff enabled _ =>
      intro e member
      rcases List.mem_append.mp member with old | added
      · exact ⟨lift (ih e old).1,lift (ih e old).2⟩
      · obtain ⟨kid,present,rfl⟩ := GeneralNominalVersionedChildren232.edge_iff.mp added
        have framed := GeneralNominalVersionedMixedAncestry237.frame enabled
        obtain ⟨raw,child,same⟩ := GeneralNominalVersionedChildren232.child_raw_site present
        exact ⟨⟨_,List.mem_append_left _ framed.raw_recorded,rfl⟩,
          ⟨raw,List.mem_append_right _ child,same⟩⟩

theorem exact_project {r : Registry} {root : Occurrence roles} {start first last : State roles}
    (source : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r) (closed : ClosedArguments (registry r))
    (one : B4Target.Steps ((boundary roles).Step r root) start first)
    (two : B4Target.Steps ((boundary roles).Step r root) start last)
    {left right : Edge roles} (seenOne : left ∈ first.core.erased.current.edges)
    (seenTwo : right ∈ last.core.erased.current.edges) (same : project left = project right) :
    left = right := by
  obtain ⟨⟨a,memA,asA⟩,⟨b,memB,asB⟩⟩ := endpoints source one left seenOne
  obtain ⟨⟨x,memX,asX⟩,⟨y,memY,asY⟩⟩ := endpoints source two right seenTwo
  have ids := Prod.mk.inj same
  have firstEq : a.occurrence.identity = x.occurrence.identity := by rw [asA,asX]; exact ids.1
  have lastEq : b.occurrence.identity = y.occurrence.identity := by rw [asB,asY]; exact ids.2
  exact Prod.ext (asA.symm.trans ((cross_trace source checked closed one two memA memX firstEq).trans asX))
    (asB.symm.trans ((cross_trace source checked closed one two memB memY lastEq).trans asY))

theorem finite_lift {α β : Type} (pool : List β) (project : α → β) (valid : α → Prop)
    (covers : ∀ x, valid x → project x ∈ pool)
    (injects : ∀ x y, valid x → valid y → project x = project y → x = y) :
    ∃ out : List α, out.length ≤ pool.length ∧ ∀ x, x ∈ out ↔ valid x := by
  classical
  let pick : β → Option α := fun id =>
    if h : ∃ x, valid x ∧ project x = id then some (Classical.choose h) else none
  refine ⟨pool.filterMap pick,List.length_filterMap_le ..,?_⟩
  intro x
  constructor
  · intro existsKey
    obtain ⟨key,_,named⟩ := List.mem_filterMap.mp existsKey
    by_cases found : ∃ y, valid y ∧ project y = key
    · change (if h : ∃ y, valid y ∧ project y = key then some (Classical.choose h) else none) = some x at named
      rw [dite_eq_left found] at named
      exact (Option.some.inj named) ▸ (Classical.choose_spec found).1
    · simp [pick,found] at named
  · intro hx
    have available : ∃ y, valid y ∧ project y = project x := ⟨x,hx,rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨project x,covers x hx,?_⟩
    have chosen := Classical.choose_spec available
    have same := injects (Classical.choose available) x chosen.1 hx chosen.2
    change (if h : ∃ y, valid y ∧ project y = project x then some (Classical.choose h) else none) = some x
    rw [dite_eq_left available,same]

def OnTrace {roles : Roles.RoleDecls} (r : Registry) (root : Occurrence roles)
    (start : State roles) (edge : Edge roles) : Prop :=
  ∃ state, B4Target.Steps ((boundary roles).Step r root) start state ∧ edge ∈ state.core.erased.current.edges

theorem finite_full_edges {r : Registry} {root : Occurrence roles} {start : State roles}
    (source : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r) (closed : ClosedArguments (registry r)) :
    ∃ edges : List (Edge roles), ∀ edge, edge ∈ edges ↔ OnTrace r root start edge := by
  obtain ⟨pool,ids⟩ := finite_projected_edges source
  obtain ⟨out,_,covers⟩ := finite_lift pool project (OnTrace r root start) (by
    rintro edge ⟨state,walk,seen⟩
    exact ids state walk edge seen) (by
    rintro first last ⟨a,one,left⟩ ⟨b,two,right⟩ same
    exact exact_project source checked closed one two left right same)
  exact ⟨out,covers⟩

end Yulang.GeneralRebaseFullEdgeBasis279
