import Yulang.GeneralRebaseProjectedReach280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebasePortCatalog280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedTrace235 (generated_registered)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralRebaseOccurrenceCode279 (DemandCode OccurrenceCode occurrenceCode outputCode)
open GeneralRebaseClosedChildShape279 (Canonical argList)
open GeneralNominalCenteredHeadMatCompletionRequests (Formed outputs)
open GeneralRebaseFixedGraph280 (Recode)
open GeneralRebaseFullEdgeBasis279 (Registered endpoints)
open GeneralRebaseRawGraph280 (source_history)
open GeneralRebaseSourceEdgeBasis279 (project)
open GeneralNominalIdentities (source)

def childId (seed parent : Nat) (d : Declaration) (c : Clause) : Nat :=
  source seed (parent,d.id,6,c.id,0)

def code (roles : Roles.RoleDecls) (seed parent : Nat) (d : Declaration) (c : Clause) : OccurrenceCode :=
  ⟨childId seed parent d c,⟨c.role,argList roles seed parent d.id c,(outputs seed parent d c).map outputCode⟩⟩

def Parents (s : State roles) : List Nat :=
  (s.core.erased.current.edges.map fun e => e.1.identity).eraseDups

def catalog (r : Registry) (seed : Nat) (root : Occurrence roles) (parents : List Nat) : List OccurrenceCode :=
  occurrenceCode root :: parents.flatMap fun parent =>
    r.declarations.flatMap fun d => d.requirements.map (code roles seed parent d)

def resolve (items : List OccurrenceCode) (id : Nat) : Option OccurrenceCode :=
  items.find? (fun item => item.identity == id)

def CodedFrom (r : Registry) (seed : Nat) (edge : Edge roles) : Prop :=
  ∃ d ∈ r.declarations, ∃ c ∈ d.requirements,
    edge.2.identity = childId seed edge.1.identity d c

theorem emitted_origin {r : Registry} {root : Occurrence roles} {s : State roles} {p : Plan roles}
    (known : GeneralNominalCenteredHeadMatCompletionRequests.Invariant r seed root s.core)
    (frame : GeneralNominalVersionedEvidence231.Frame r s.core p.packet.site.occurrence p.packet.declaration.id p)
    (added : edge ∈ GeneralNominalVersionedChildren232.edges p) :
    CodedFrom r seed edge := by
  obtain ⟨kid,member,rfl⟩ := GeneralNominalVersionedChildren232.edge_iff.mp added
  obtain ⟨site,present,rfl⟩ := GeneralNominalVersionedChildren232.emitted_child_iff.mp member
  unfold GeneralNominalVersionedChildren232.emitted at present
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp present
  refine ⟨p.packet.declaration,frame.visible,c.val,
    (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property,?_⟩
  change GeneralNominalIdentities.source p.packet.context.state.seed _ = _
  rw [frame.context_eq,known.seed_eq]
  rfl

theorem origins_trace {r : Registry} {root : Occurrence roles} {s : State roles}
    (path : B4Target.Steps (Step r root) (initial ctx root) s) :
    ∀ edge ∈ s.core.erased.current.edges, CodedFrom r ctx.state.seed edge := by
  induction path with
  | refl => intro edge seen; cases seen
  | tail path action ih =>
    obtain ⟨focus,generated,atStep⟩ := action
    cases atStep with
    | administrative admin =>
      cases admin <;> exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      intro edge member
      rcases List.mem_append.mp member with old|added
      · exact ih edge old
      · exact emitted_origin (GeneralNominalVersionedMixedCompletionRequests235.trace path)
          (GeneralNominalVersionedMixedAncestry237.frame enabled) added

theorem origins_source {r : Registry} {root : Occurrence roles} {start s : State roles}
    (initialSource : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s)
    (seen : edge ∈ s.core.erased.current.edges) :
    CodedFrom (registry r) start.core.erased.current.context.state.seed edge := by
  obtain ⟨legacy,⟨ctx,_,_,_,_,_,rfl⟩,rfl⟩ := initialSource
  exact origins_trace path edge seen

theorem parent_member {s : State roles} (seen : edge ∈ s.core.erased.current.edges) :
    edge.1.identity ∈ Parents s :=
  List.mem_eraseDups.mpr (List.mem_map.mpr ⟨edge,seen,rfl⟩)

theorem child_mem {r : Registry} {root : Occurrence roles} {parents : List Nat}
    (hasParent : parent ∈ parents) (visible : d ∈ r.declarations) (child : c ∈ d.requirements) :
    code roles seed parent d c ∈ catalog r seed root parents := by
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨parent,hasParent,List.mem_flatMap.mpr ⟨d,visible,List.mem_map.mpr ⟨c,child,rfl⟩⟩⟩

theorem handles_registered {r : Registry} {root : Occurrence roles} {start s : State roles}
    (initialSource : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s)
    (record : Registered s raw) :
    ∃ item ∈ catalog (registry r) start.core.erased.current.context.state.seed root (Parents s),
      item.identity = raw.identity := by
  obtain ⟨site,mem,rfl⟩ := record
  rcases (source_history initialSource path).incoming site mem with eq | ⟨parent,incoming⟩
  · exact ⟨occurrenceCode root,List.mem_cons_self,congrArg Occurrence.identity eq.symm⟩
  · obtain ⟨d,visible,c,chosen,eq⟩ := origins_source initialSource path incoming
    exact ⟨code roles _ parent.identity d c, child_mem (parent_member incoming) visible chosen, eq.symm⟩

theorem resolve_complete {items : List OccurrenceCode} {id : Nat} (member : x ∈ items)
    (idEq : x.identity = id) :
    ∃ found, resolve items id = some found := by
  cases eq : resolve items id with
  | none =>
    have missing := List.find?_eq_none.mp eq x member
    exact False.elim (missing (by simp [idEq]))
  | some a => exact ⟨a,rfl⟩

theorem resolve_sound {items : List OccurrenceCode} {id : Nat}
    (read : resolve items id = some x) : x ∈ items ∧ x.identity = id := by
  induction items with
  | nil => cases read
  | cons a rest ih =>
    by_cases same : a.identity = id
    · have eq : a = x := by simpa [resolve,List.find?_cons,same] using read
      subst a
      exact ⟨List.mem_cons_self,same⟩
    · have eq : resolve rest id = some x := by
        simpa [resolve,List.find?_cons,same] using read
      exact ⟨List.mem_cons_of_mem _ (ih eq).1,(ih eq).2⟩

theorem resolve_registered {r : Registry} {root : Occurrence roles} {start s : State roles}
    (initialSource : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s)
    (record : Registered s raw) :
    ∃ found, resolve (catalog (registry r) start.core.erased.current.context.state.seed root (Parents s))
      raw.identity = some found := by
  obtain ⟨x,h,eq⟩ := handles_registered initialSource path record
  exact resolve_complete h eq

end Yulang.GeneralRebasePortCatalog280
