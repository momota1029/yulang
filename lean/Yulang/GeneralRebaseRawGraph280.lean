import Yulang.GeneralRebaseFixedGraph280

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRawGraph280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedTrace235 (generated_registered)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseFullEdgeBasis279 (Registered)

def Incoming (state : State roles) (root focus : Occurrence roles) : Prop :=
  focus = root ∨ ∃ parent, (parent,focus) ∈ state.core.erased.current.edges

structure History (state : State roles) (root : Occurrence roles) : Prop where
  incoming : ∀ raw ∈ state.core.erased.current.sites, Incoming state root raw.occurrence
  edges : ∀ edge ∈ state.core.erased.current.edges, Generated state.core.erased.current root edge.1

theorem traces {r : Registry} {root : Occurrence roles} {s : State roles}
    (path : B4Target.Steps (Step r root) (initial context root) s) :
    History s root := by
  induction path with
  | refl =>
    refine ⟨?_,?_⟩
    · intro raw seen
      cases List.mem_singleton.mp seen
      exact Or.inl rfl
    · intro edge member
      cases member
  | @tail before after path step ih =>
    have grow := GeneralNominalVersionedMixedGrowth234.step step
    obtain ⟨focus,generated,atStep⟩ := step
    have carry : ∀ target, Generated before.core.erased.current root target →
        Generated after.core.erased.current root target := fun _ seen =>
      GeneralNominalVersionedMixedGrowth234.generated grow seen
    have lift {target : Occurrence roles} (old : Incoming before root target) : Incoming after root target := by
      rcases old with rfl|⟨p,edge⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨p,grow.edges edge⟩
    cases atStep with
    | administrative admin =>
      cases admin with
      | enqueue _ absent =>
        obtain ⟨raw,present,same⟩ := generated_registered
          (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
        exact False.elim (absent raw present same)
      | refresh | equate | reobserve =>
        exact ⟨fun raw present => lift (ih.incoming raw present),fun edge mem => carry _ (ih.edges edge mem)⟩
    | refresh | merge =>
      exact ⟨fun raw present => lift (ih.incoming raw present),fun edge mem => carry _ (ih.edges edge mem)⟩
    | install effect enabled novel =>
      refine ⟨?_,?_⟩
      · intro raw mem
        rcases List.mem_append.mp mem with old | added
        · exact lift (ih.incoming raw old)
        · change raw ∈ (GeneralNominalVersionedChildren232.emitted effect.plan).map Site.observed at added
          obtain ⟨site,present,rfl⟩ := List.mem_map.mp added
          have child : site.occurrence ∈ GeneralNominalVersionedFrame231.children effect.plan.packet :=
            GeneralNominalVersionedChildren232.emitted_child_iff.mpr ⟨site,present,rfl⟩
          exact Or.inr ⟨_,GeneralNominalVersionedInstall232.installed_child child⟩
      · intro edge mem
        rcases List.mem_append.mp mem with old | added
        · exact carry _ (ih.edges edge old)
        · obtain ⟨kid,_,rfl⟩ := GeneralNominalVersionedChildren232.edge_iff.mp added
          exact carry _ generated

theorem source_history {r : Registry} {root : Occurrence roles} {start s : State roles}
    (source : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s) :
    History s root := by
  obtain ⟨legacy,⟨context,_,_,_,_,_,rfl⟩,rfl⟩ := source
  exact traces path

theorem registered_generated {r : Registry} {root : Occurrence roles} {start s : State roles}
    (source : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s) (focus : Occurrence roles) :
    Registered s focus ↔ Generated s.core.erased.current root focus := by
  constructor
  · rintro ⟨raw,seen,rfl⟩
    have h := source_history source path
    rcases h.incoming raw seen with same|⟨p,edge⟩
    · rw [same]
      exact .root
    · exact .child (h.edges (p,raw.occurrence) edge) edge
  · exact generated_registered (GeneralNominalVersionedMixedTrace235.reachable ⟨start,source,path⟩).1

end Yulang.GeneralRebaseRawGraph280
