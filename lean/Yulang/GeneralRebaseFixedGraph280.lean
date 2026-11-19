import Yulang.GeneralRebaseChildPorts280
import Yulang.GeneralRebaseFullEdgeBasis279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseFixedGraph280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedTrace235 (generated_registered)
open GeneralNominalCenteredHeadMatCompletionRequests (Formed formed_above)
open GeneralRebaseClosedChildShape279 (Canonical)
open GeneralRebaseFullEdgeBasis279 (Registered endpoints finite_lift)
open GeneralRebaseSourceEdgeBasis279 (project finite_projected_edges)
open GeneralRebaseChildPorts280
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalCenteredHeadAllocEncoding (registry)

structure Recode (r : Registry) (seed : Nat) (root raw target : Occurrence roles) : Prop where
  canonical : Canonical r seed root target
  formed : Formed r seed root target
  identity : raw.identity = target.identity
  role : raw.demand.role = target.demand.role
  outputs : raw.demand.outputs = target.demand.outputs

theorem root_recode (r : Registry) (seed : Nat) (root : Occurrence roles) :
    Recode r seed root root root :=
  ⟨Or.inl rfl,Or.inl rfl,rfl,rfl,rfl⟩

theorem child_recode {r : Registry} {root : Occurrence roles} {state : State roles} {p : Plan roles}
    (inv : GeneralNominalCenteredHeadMatCompletionRequests.Invariant r seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame r state.core p.packet.site.occurrence p.packet.declaration.id p)
    (member : c ∈ p.packet.declaration.requirements) (valid : c.Signature roles) :
    Recode r seed root (GeneralNominalVersionedFrame231.clauseChild p.packet c valid) (fixed p.packet c valid) := by
  have seedEq : p.packet.context.state.seed = seed := by rw [frame.context_eq,inv.seed_eq]
  have above : root.identity ≤ p.packet.site.occurrence.identity := formed_above (inv.raw _ frame.raw_recorded)
  exact ⟨fixed_canonical p.packet c valid frame.visible member above seedEq,
    fixed_formed p.packet c valid frame.visible member above seedEq,rfl,rfl,rfl⟩

theorem child_exists {r : Registry} {root : Occurrence roles} {state : State roles} {p : Plan roles}
    (inv : GeneralNominalCenteredHeadMatCompletionRequests.Invariant r seed root state.core)
    (frame : GeneralNominalVersionedEvidence231.Frame r state.core p.packet.site.occurrence p.packet.declaration.id p)
    (member : raw ∈ GeneralNominalVersionedChildren232.rawSites p) :
    ∃ canon, Recode r seed root raw.occurrence canon := by
  change raw ∈ (GeneralNominalVersionedChildren232.emitted p).map Site.observed at member
  obtain ⟨site,inEmitted,rfl⟩ := List.mem_map.mp member
  unfold GeneralNominalVersionedChildren232.emitted at inEmitted
  obtain ⟨clause,_,rfl⟩ := List.mem_map.mp inEmitted
  have mentioned := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  exact ⟨_,child_recode inv frame mentioned _⟩

theorem same_id {r : Registry} {root a b x y : Occurrence roles}
    (checked : Checked r) (one : Recode r seed root a x) (two : Recode r seed root b y)
    (equal : a.identity = b.identity) : x = y :=
  GeneralRebaseClosedChildIdentity279.exact checked one.canonical two.canonical one.formed two.formed
    (one.identity.symm.trans (equal.trans two.identity))

theorem recode_trace {r : Registry} {root : Occurrence roles} {state : State roles}
    (path : B4Target.Steps (Step r root) (initial context root) state) :
    ∀ raw ∈ state.core.erased.current.sites, ∃ target, Recode r context.state.seed root raw.occurrence target := by
  induction path with
  | refl =>
    intro raw registered
    cases List.mem_singleton.mp registered
    exact ⟨root,root_recode r context.state.seed root⟩
  | tail path action ih =>
    obtain ⟨focus,generated,step⟩ := action
    cases step with
    | administrative admin =>
      cases admin with
      | enqueue _ absent =>
        obtain ⟨raw,present,same⟩ := generated_registered
          (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
        exact False.elim (absent raw present same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install e enabled _ =>
      intro raw recorded
      rcases List.mem_append.mp recorded with old | new
      · exact ih raw old
      · exact child_exists (GeneralNominalVersionedMixedCompletionRequests235.trace path)
          (GeneralNominalVersionedMixedAncestry237.frame enabled) new

theorem source_recode {r : Registry} {root : Occurrence roles} {start state : State roles}
    (source : (boundary roles).Initial r root start)
    (walk : B4Target.Steps ((boundary roles).Step r root) start state)
    (raw : Registered state focus) :
    ∃ target, Recode (registry r) start.core.erased.current.context.state.seed root focus target := by
  obtain ⟨legacy,⟨context,_,_,_,_,_,rfl⟩,rfl⟩ := source
  obtain ⟨site,member,rfl⟩ := raw
  exact recode_trace walk site member

structure RecodeEdge (r : Registry) (seed : Nat) (root : Occurrence roles) (raw fixed : Edge roles) : Prop where
  first : Recode r seed root raw.1 fixed.1
  last : Recode r seed root raw.2 fixed.2

theorem edge_projection {raw normalized : Edge roles} (matchEdge : RecodeEdge r seed root raw normalized) :
    project raw = project normalized :=
  Prod.ext matchEdge.first.identity matchEdge.last.identity

theorem source_edge {r : Registry} {root : Occurrence roles} {start state : State roles}
    (source : (boundary roles).Initial r root start)
    (walk : B4Target.Steps ((boundary roles).Step r root) start state)
    (seen : raw ∈ state.core.erased.current.edges) :
    ∃ fixed, RecodeEdge (registry r) start.core.erased.current.context.state.seed root raw fixed := by
  obtain ⟨first,last⟩ := endpoints source walk raw seen
  obtain ⟨a,left⟩ := source_recode source walk first
  obtain ⟨b,right⟩ := source_recode source walk last
  exact ⟨(a,b),left,right⟩

def CanonicalOnTrace {roles : Roles.RoleDecls} (r : Registry) (root : Occurrence roles)
    (start : State roles) (fixed : Edge roles) : Prop :=
  ∃ state, B4Target.Steps ((boundary roles).Step r root) start state ∧
    ∃ raw ∈ state.core.erased.current.edges,
      RecodeEdge (registry r) start.core.erased.current.context.state.seed root raw fixed

theorem project_unique {r : Registry} {root : Occurrence roles} {start : State roles}
    (checked : (boundary roles).Checked r)
    (a : CanonicalOnTrace r root start first) (b : CanonicalOnTrace r root start last)
    (same : project first = project last) : first = last := by
  obtain ⟨_,_,_,_,one⟩ := a
  obtain ⟨_,_,_,_,two⟩ := b
  have p := (edge_projection one).trans (same.trans (edge_projection two).symm)
  have checked' := (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
  exact Prod.ext (same_id checked' one.first two.first (congrArg Prod.fst p))
    (same_id checked' one.last two.last (congrArg Prod.snd p))

theorem finite_canonical_edges {r : Registry} {root : Occurrence roles} {start : State roles}
    (source : (boundary roles).Initial r root start) (checked : (boundary roles).Checked r) :
    ∃ edges : List (Edge roles), ∀ e, e ∈ edges ↔ CanonicalOnTrace r root start e := by
  obtain ⟨pool,covers⟩ := finite_projected_edges source
  obtain ⟨out,_,exactly⟩ := finite_lift pool project (CanonicalOnTrace r root start) (by
    rintro edge ⟨state,path,raw,seen,recoded⟩
    rw [← edge_projection recoded]
    exact covers state path raw seen) (fun _ _ a b same => project_unique checked a b same)
  exact ⟨out,exactly⟩

end Yulang.GeneralRebaseFixedGraph280
