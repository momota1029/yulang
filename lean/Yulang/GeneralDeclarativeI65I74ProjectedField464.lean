import Yulang.GeneralDeclarativeI65I74NamedProjection464
import Yulang.GeneralDeclarativeI65I74IssuedProjection464
import Yulang.GeneralDeclarativeI65I74PreparedTableTransport463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open PreparedDeclarations463
open RetainedFull445 (FullProblem)
open PhysicalVisit463 PhysicalVisit463.IssuedProjection464
open WrittenPattern460
open RecordTraversal455.MixedQA (ChildAt)
open RoutedInlineStructural458 (ModelOpening)

/-- Only an input pair of already supplied snapshots. The exact same
authored registry and request are premises of this bridge, not something a
candidate wire can establish. No canonical problem or graph is produced. -/
structure SnapshotPair where
  before : FullProblem
  after : FullProblem
  registry : authoredRegistry before.state.base.core.current =
    authoredRegistry after.state.base.core.current
  root : before.root = after.root

def SnapshotPair.pre (p : SnapshotPair) := p.before.state.base.core.current.ordinary
def SnapshotPair.post (p : SnapshotPair) := p.after.state.base.core.current.ordinary

def SnapshotPair.afterTable (p : SnapshotPair) (t : CheckedTable p.before.state.base.core.current) :
    CheckedTable p.after.state.base.core.current :=
  reindexCheckedTable p.registry t

theorem same_authored_roster_and_original_head_arguments (p : SnapshotPair) :
    visible p.before.old.state.core p.before.root = visible p.after.old.state.core p.after.root ∧
    p.before.root.demand.arguments = p.after.root.demand.arguments := by
  exact ⟨by
    change (List.filter (fun d => d.role == p.before.root.demand.role)
      (authoredRegistry p.before.state.base.core.current).declarations) =
      (List.filter (fun d => d.role == p.after.root.demand.role)
      (authoredRegistry p.after.state.base.core.current).declarations)
    rw [p.root,p.registry],congrArg (fun q : I72.Request => q.demand.arguments) p.root⟩

structure ProjectionFieldWire (p : SnapshotPair) where
  projection : ProjectionWire
  hop : Nat
  field : HeadFieldWire p.after.old

structure ProjectionFieldReceipt where
  hop : Nat
  field : HeadFieldReceipt

def readProjectionField (p : SnapshotPair) (t : CheckedTable p.before.state.base.core.current)
    (site : Nat) (w : ProjectionFieldWire p) : Option ProjectionFieldReceipt := do
  if !checkProjection p.pre p.post site w.projection then none else
    let r ← readHeadField (p := p.after.old) (p.afterTable t) w.field
    if r.rows[w.hop]? = some p.pre.equations.length then
      some ⟨w.hop,r⟩
    else none

/-- Physical occurrence at the chosen hop (possibly not the first) must
use the exact appended ordinal in the existing after-state derivation.
These are not general resolver rules or admission completeness. -/
def ExactProjectedField (p : SnapshotPair) (t : CheckedTable p.before.state.base.core.current)
    (site : Nat) (r : ProjectionFieldReceipt) : Prop :=
  ProjectionAt p.pre p.post site ∧
    ExactHeadField (p := p.after.old) (p.afterTable t) r.field ∧
    r.field.rows[r.hop]? = some p.pre.equations.length

theorem exact_projected_field_iff_finite_checked_wire
    (p : SnapshotPair) (t : CheckedTable p.before.state.base.core.current)
    (site : Nat) (r : ProjectionFieldReceipt) :
    ExactProjectedField p t site r ↔ ∃ w, readProjectionField p t site w = some r := by
  constructor
  · rintro ⟨proper,field,row⟩
    obtain ⟨proof,projection⟩ := (independent_one_row_projection_iff_finite_data ..).mpr proper
    obtain ⟨w,look⟩ := (prechecked_head_field_iff_finite_exact_wire ..).mp field
    exact ⟨⟨proof,r.hop,w⟩,by cases r; simp_all [readProjectionField,Option.bind]⟩
  · rintro ⟨w,read⟩
    by_cases proper : checkProjection p.pre p.post site w.projection = true
    · cases look : readHeadField (p := p.after.old) (p.afterTable t) w.field with
      | none => simp [readProjectionField,proper,look,Option.bind] at read
      | some field =>
        by_cases row : field.rows[w.hop]? = some p.pre.equations.length
        · have eq : (⟨w.hop,field⟩ : ProjectionFieldReceipt) = r := by
            simpa [readProjectionField,proper,look,row,Option.bind] using read
          cases eq
          exact ⟨(independent_one_row_projection_iff_finite_data ..).mp ⟨_,proper⟩,
            (prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨_,look⟩,row⟩
        · simp [readProjectionField,proper,look,row,Option.bind] at read
    · simp [readProjectionField,proper] at read

theorem literal_post_visit_keeps_an_old_cycle_and_the_exact_issued_native_site
    {p : SnapshotPair} {t : CheckedTable p.before.state.base.core.current}
    {site : Nat} {r : ProjectionFieldReceipt} (h : ExactProjectedField p t site r)
    (m : I72.Model) (fit : FitsFull p.after.state m) :
    r.field.literal ≠ [] ∧ AliasCycle p.pre (observed p.pre) r.field.terminal ∧
    ∃ logical query row shape addr child next used origin,
      r.field.path[r.hop]? = some (addr,child) ∧
      p.post.equations[p.pre.equations.length]? = some row ∧ row.left = site ∧
      GeneralDeclarativeLowerKnown321.Alias p.post logical site ∧
      shapeOf row.right = some shape ∧ ChildAt shape query addr child next ∧
      origin ∈ p.after.state.base.core.origins ∧ OriginRoute p.after.state.base.core origin logical ∧
      origin.slot = site ∧ m.nativeSyntax origin.slot = some origin.endpoint ∧
      ModelOpening p.after.state.base.core m logical row shape query addr child next used := by
  obtain ⟨hmodel,last,_,nonempty,source,cycle⟩ :=
    exact_prechecked_head_field_keeps_original_and_evidence_in_each_fit
      ⟨p.after,p.afterTable t⟩ h.2.1 m fit
  refine ⟨nonempty,(exact_projection_keeps_all_raw_k2_sites h.1 _).mp cycle,?_⟩
  obtain ⟨auth,endPattern,_,trail,_,_,_⟩ := h.2.1
  obtain ⟨logical,query,row,shape,addr,child,next,used,origin,pick,store,link,formed,reads,
    allowed,issued,route,physical,native,model⟩ :=
    selected_index_keeps_the_exact_issued_owner_in_the_same_fit trail m fit.1 h.2.2
  obtain ⟨stored,exactOrdinal,owner⟩ := (exact_projection_retains_old_raw_ordinals_and_the_actual_new_slot h.1).2
  have same : stored = row := Option.some.inj (exactOrdinal.symm.trans store)
  subst stored
  exact ⟨logical,query,row,shape,addr,child,next,used,origin,pick,store,owner,owner ▸ link,formed,reads,
    issued,route,physical.trans owner,native,model⟩

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
