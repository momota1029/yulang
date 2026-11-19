import Yulang.GeneralRebasePortCatalog280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseFixedGraphExec280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCenteredHeadMatCompletionRequests (Formed outputs formed_above)
open GeneralRebaseOccurrenceCode279 (OccurrenceCode occurrenceCode)
open GeneralRebasePortCatalog280
open GeneralRebaseChildPorts280 (ports)
open GeneralRebaseClosedChildShape279 (Canonical)
open GeneralRebaseFixedGraph280 (Recode RecodeEdge)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralRebaseFullEdgeBasis279 (Registered endpoints)

def occurrence (roles : Roles.RoleDecls) (seed parent : Nat) (d : Declaration) (c : Clause)
    (valid : c.Signature roles) : Occurrence roles :=
  ⟨childId seed parent d c,⟨c.role,fun i => ports seed parent d.id c.id i.val,
    outputs seed parent d c,by
      intro o member
      obtain ⟨eq,listed,rfl⟩ := List.mem_map.mp member
      exact valid.2 eq listed⟩⟩

theorem occ_code (roles : Roles.RoleDecls) (seed parent : Nat) (d : Declaration) (c : Clause)
    (valid : c.Signature roles) :
    occurrenceCode (occurrence roles seed parent d c valid) = code roles seed parent d c := rfl

theorem parents_above {r : Registry} {root : Occurrence roles} {start s : State roles}
    (initialSource : (boundary roles).Initial r root start)
    (path : B4Target.Steps ((boundary roles).Step r root) start s) :
    ∀ p ∈ Parents s, root.identity ≤ p := by
  intro p member
  obtain ⟨edge,present,rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp member)
  obtain ⟨canon,matched⟩ := GeneralRebaseFixedGraph280.source_recode initialSource path (endpoints initialSource path edge present).1
  rw [matched.identity]
  exact formed_above matched.formed

theorem catalog_reify {roles : Roles.RoleDecls} {root : Occurrence roles}
    (r : Registry) (checked : Checked r) (sameRoles : r.roles = roles)
    (parents : List Nat) (bounds : ∀ p ∈ parents, root.identity ≤ p)
    (item : OccurrenceCode) (mem : item ∈ catalog r seed root parents) :
    ∃ o : Occurrence roles, occurrenceCode o = item ∧ Canonical r seed root o ∧ Formed r seed root o := by
  rcases List.mem_cons.mp mem with rfl|made
  · exact ⟨root,rfl,Or.inl rfl,Or.inl rfl⟩
  · obtain ⟨p,known,inRegistry⟩ := List.mem_flatMap.mp made
    obtain ⟨d,visible,inDecl⟩ := List.mem_flatMap.mp inRegistry
    obtain ⟨c,belongs,rfl⟩ := List.mem_map.mp inDecl
    have sig : c.Signature roles := sameRoles ▸ (checked.2 d visible).signature.2.2.2 c belongs
    exact ⟨occurrence roles seed p d c sig,rfl,
      Or.inr ⟨p,d,visible,c,belongs,bounds p known,rfl,rfl,rfl⟩,
      Or.inr ⟨p,d,visible,c,belongs,bounds p known,rfl,rfl⟩⟩

theorem exact_read {r : Registry} {root raw canon : Occurrence roles} {start s : State roles}
    (initialSource : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r)
    (path : B4Target.Steps ((boundary roles).Step r root) start s)
    (registered : Registered s raw)
    (normalized : Recode (registry r) start.core.erased.current.context.state.seed root raw canon) :
    resolve (catalog (registry r) start.core.erased.current.context.state.seed root (Parents s)) raw.identity =
      some (occurrenceCode canon) := by
  obtain ⟨item,read⟩ := resolve_registered initialSource path registered
  have found := resolve_sound read
  have valid := checked_compiled checked
  obtain ⟨o,h,co,fo⟩ := catalog_reify _ valid.2 valid.1 _ (parents_above initialSource path) item found.1
  have same : o.identity = canon.identity :=
    (congrArg OccurrenceCode.identity h).trans (found.2.trans normalized.identity)
  have exactO := GeneralRebaseClosedChildIdentity279.exact valid.2 co normalized.canonical fo normalized.formed same
  rw [← h,exactO] at read
  exact read

abbrev EdgeCode := OccurrenceCode × OccurrenceCode
def recode (items : List OccurrenceCode) (e : Edge roles) : Option EdgeCode := do
  let left ← resolve items e.1.identity
  let right ← resolve items e.2.identity
  pure (left,right)

def edgeCodes (r : Registry) (seed : Nat) (root : Occurrence roles) (s : State roles) : List EdgeCode :=
  (s.core.erased.current.edges.filterMap (recode (catalog r seed root (Parents s)))).eraseDups

def edgeCode (e : Edge roles) : EdgeCode := (occurrenceCode e.1,occurrenceCode e.2)

theorem write_exact {r : Registry} {root : Occurrence roles} {start s : State roles}
    (initialSource : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r)
    (path : B4Target.Steps ((boundary roles).Step r root) start s)
    (present : raw ∈ s.core.erased.current.edges)
    (normalized : RecodeEdge (registry r) start.core.erased.current.context.state.seed root raw canon) :
    recode (catalog (registry r) start.core.erased.current.context.state.seed root (Parents s)) raw =
      some (edgeCode canon) := by
  have parts := endpoints initialSource path raw present
  unfold recode edgeCode
  rw [exact_read initialSource checked path parts.1 normalized.first,
      exact_read initialSource checked path parts.2 normalized.last]
  rfl

theorem edges_exact {r : Registry} {root : Occurrence roles} {start s : State roles}
    (initialSource : (boundary roles).Initial r root start)
    (checked : (boundary roles).Checked r)
    (path : B4Target.Steps ((boundary roles).Step r root) start s) (out : EdgeCode) :
    out ∈ edgeCodes (registry r) start.core.erased.current.context.state.seed root s ↔
    ∃ raw ∈ s.core.erased.current.edges, ∃ canon,
      RecodeEdge (registry r) start.core.erased.current.context.state.seed root raw canon ∧ edgeCode canon = out := by
  unfold edgeCodes
  rw [List.mem_eraseDups,List.mem_filterMap]
  constructor
  · rintro ⟨raw,present,read⟩
    obtain ⟨canon,valid⟩ := GeneralRebaseFixedGraph280.source_edge initialSource path present
    exact ⟨raw,present,canon,valid,Option.some.inj ((write_exact initialSource checked path present valid).symm.trans read)⟩
  · rintro ⟨raw,present,canon,valid,rfl⟩
    exact ⟨raw,present,write_exact initialSource checked path present valid⟩

end Yulang.GeneralRebaseFixedGraphExec280
