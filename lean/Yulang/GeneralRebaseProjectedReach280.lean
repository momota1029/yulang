import Yulang.GeneralRebaseRawGraph280

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseProjectedReach280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedTrace235 (generated_registered)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseFullEdgeBasis279 (Registered endpoints)
open GeneralRebaseRawGraph280 (source_history registered_generated History)
open GeneralRebaseSourceEdgeBasis279 (project)

def ids (state : State roles) : List (Nat × Nat) :=
  (state.core.erased.current.edges.map project).eraseDups

inductive Reached (root : Nat) (edges : List (Nat × Nat)) : Nat → Prop
  | root : Reached root edges root
  | child : Reached root edges parent → (parent,next) ∈ edges → Reached root edges next

theorem edges_mem (s : State roles) :
    edge ∈ ids s ↔ ∃ raw ∈ s.core.erased.current.edges, project raw = edge := by
  unfold ids
  rw [List.mem_eraseDups,List.mem_map]

theorem child_edge (s : State roles) (seen : (parent,next) ∈ s.core.erased.current.edges) :
    (parent.identity,next.identity) ∈ ids s :=
  (edges_mem s).mpr ⟨_,seen,rfl⟩

theorem exists_raw {r : Registry} {root : Occurrence roles} {start s : State roles}
    (source : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s)
    (seen : Reached root.identity (ids s) target) :
    ∃ raw, Registered s raw ∧ raw.identity = target := by
  cases seen with
  | root =>
    exact ⟨root,(registered_generated source path root).mpr .root,rfl⟩
  | child old linked =>
    obtain ⟨e,has,eq⟩ := (edges_mem s).mp linked
    exact ⟨e.2,(endpoints source path e has).2,congrArg Prod.snd eq⟩

theorem Reached.lift {root target : Nat} {a b : List (Nat × Nat)} (old : a ⊆ b)
    (seen : Reached root a target) : Reached root b target := by
  induction seen with
  | root => exact .root
  | child _ edge ih => exact .child ih (old edge)

theorem ids_growth (action : Step r root before after) : ids before ⊆ ids after := by
  intro edge has
  obtain ⟨raw,old,same⟩ := (edges_mem before).mp has
  exact (edges_mem after).mpr ⟨raw,(GeneralNominalVersionedMixedGrowth234.step action).edges old,same⟩

theorem traced {r : Registry} {root : Occurrence roles} {state : State roles}
    (path : B4Target.Steps (Step r root) (initial context root) state) :
    ∀ site ∈ state.core.erased.current.sites, Reached root.identity (ids state) site.occurrence.identity := by
  induction path with
  | refl =>
    intro site stored
    cases List.mem_singleton.mp stored
    exact .root
  | @tail before after path action ih =>
    have grow := ids_growth action
    obtain ⟨focus,generated,atStep⟩ := action
    have recorded := (GeneralNominalVersionedMixedTrace235.steps
      (GeneralNominalVersionedMixedTrace235.initial context) path).1
    cases atStep with
    | administrative admin =>
      cases admin with
      | enqueue _ absent =>
        obtain ⟨site,seen,rfl⟩ := generated_registered recorded generated
        exact False.elim (absent site seen rfl)
      | refresh | equate | reobserve =>
        exact fun _ stored => (ih _ stored).lift grow
    | refresh | merge =>
      exact fun _ stored => (ih _ stored).lift grow
    | install effect enabled novel =>
      intro site stored
      rcases List.mem_append.mp stored with old | new
      · exact (ih _ old).lift grow
      · change site ∈ (GeneralNominalVersionedChildren232.emitted effect.plan).map Site.observed at new
        obtain ⟨child,isChild,rfl⟩ := List.mem_map.mp new
        have member := GeneralNominalVersionedChildren232.emitted_child_iff.mpr ⟨child,isChild,rfl⟩
        have edge := GeneralNominalVersionedInstall232.installed_child (state := before) (effect := effect) member
        obtain ⟨raw,earlier,same⟩ := generated_registered recorded generated
        exact .child ((same ▸ ih raw earlier).lift grow) (child_edge _ edge)

theorem source_reach_exact {r : Registry} {root : Occurrence roles} {start state : State roles}
    (source : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start state) :
    Reached root.identity (ids state) target ↔
      ∃ focus, Generated state.core.erased.current root focus ∧ focus.identity = target := by
  constructor
  · intro seen
    obtain ⟨raw,recorded,eq⟩ := exists_raw source path seen
    exact ⟨raw,(registered_generated source path raw).mp recorded,eq⟩
  · rintro ⟨focus,generated,rfl⟩
    have ⟨raw,recorded,same⟩ := (registered_generated source path focus).mpr generated
    obtain ⟨legacy,⟨context,_,_,_,_,_,rfl⟩,rfl⟩ := source
    rw [← same]
    exact traced path raw recorded

end Yulang.GeneralRebaseProjectedReach280
