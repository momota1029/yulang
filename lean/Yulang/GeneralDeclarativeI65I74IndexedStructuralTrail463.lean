import Yulang.GeneralDeclarativeI65I74IndexedPhysicalVisit463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
open WrittenPattern460
open RecordTraversal455 (RawSnapshot termInspects term_inspects_exact455)
open RecordTraversal455.MixedQA (MixedPath)
open AuthenticatedHop458 (Policy readStep)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeInspect321 (Inspects)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open SplitEscape446 (splitCheck446 checked_split_escape_excludes_exact_raw_K2446)
open SplitEscape446.SplitCompact447 (raw_safe_iff_small_witness447)

/-- The original structural coordinate and exact selected physical row are
kept together. Only the actual selected hop is traversed. -/
inductive IndexedJoint (s : RawSnapshot) (pol : Policy) (keys : Nat → KeyRead) :
    Nat → Term → Expr → MixedPath → List Nat → Nat → Term → Bool → Prop where
  | stop : Inspects code → IndexedJoint s pol keys root term code [] [] root term false
  | down : ¬ AliasCycle s (observed s) root →
      IndexedOpen s pol root code ordinal addr child next used →
      Step (keys root) term (writtenAddress addr) selected →
      IndexedJoint s pol keys child selected next tail physical terminal final more →
      IndexedJoint s pol keys root term code ((addr,child)::tail) (ordinal::physical) terminal final (used || more)

def indexedRows {pol : Policy} :
    JointWire pol inheritedCompilerPlacement → List Nat
  | .stop _ => []
  | .down _ hop _ tail => hop.row :: indexedRows tail

private theorem neutral_action (root : Nat) (t : Term) (q : Expr) (u : Unit) :
    inheritedCompilerPlacement.checks root t q u = true := by cases u; rfl

theorem read_same_wire_preserves_every_selected_physical_index
    {s pol keys root term code path terminal final used}
    {w : JointWire pol inheritedCompilerPlacement}
    (read : readJoint s pol keys inheritedCompilerPlacement root term code w = some (path,terminal,final,used)) :
    IndexedJoint s pol keys root term code path (indexedRows w) terminal final used := by
  induction w generalizing root term code path terminal final used with
  | stop u =>
    by_cases allowed : termInspects code = true
    · simp [readJoint,neutral_action,allowed] at read
      obtain ⟨rfl,rfl,rfl,rfl⟩ := read
      exact .stop ((term_inspects_exact455 _).mp allowed)
    · simp [readJoint,neutral_action,allowed] at read
  | down u hop cut rest ih =>
    by_cases safe : splitCheck446 s root cut = true
    · cases start : AuthenticatedHop458.readStep s pol root code hop with
      | none => simp [readJoint,neutral_action,safe,start,Option.bind] at read
      | some raw =>
        obtain ⟨a,c,nxt,mark⟩ := raw
        cases written : WrittenPattern460.readStep (keys root) term (writtenAddress a) with
        | none => simp [readJoint,neutral_action,safe,start,written,Option.bind] at read
        | some chosen =>
          cases follow : readJoint s pol keys inheritedCompilerPlacement c chosen nxt rest with
          | none => simp [readJoint,neutral_action,safe,start,written,follow,Option.bind] at read
          | some later =>
            obtain ⟨trail,n,l,tag⟩ := later
            simp [readJoint,neutral_action,safe,start,written,follow,Option.bind] at read
            obtain ⟨rfl,rfl,rfl,rfl⟩ := read
            exact .down (checked_split_escape_excludes_exact_raw_K2446 safe)
              (raw_witness_reads_its_identical_physical_row start) (read_step_sound written) (ih follow)
    · simp [readJoint,neutral_action,safe] at read

theorem exact_indexed_structural_route_has_same_order_finite_wire
    {s pol keys root term code path physical terminal final used}
    (read : IndexedJoint s pol keys root term code path physical terminal final used) :
    ∃ w : JointWire pol inheritedCompilerPlacement, indexedRows w = physical ∧
      readJoint s pol keys inheritedCompilerPlacement root term code w = some (path,terminal,final,used) := by
  induction read with
  | stop rigid =>
    exact ⟨.stop (),rfl,by simp [readJoint,neutral_action,(term_inspects_exact455 _).mpr rigid]⟩
  | down safe actual located _ ih =>
    obtain ⟨hop,row,reads⟩ := an_exact_physical_row_reifies_at_the_same_index actual
    obtain ⟨cut,hold,_,_⟩ := (raw_safe_iff_small_witness447 s _).mp safe
    obtain ⟨tail,rows,follows⟩ := ih
    exact ⟨.down () hop cut tail,by simp [indexedRows,row,rows],
      by simp [readJoint,neutral_action,hold,reads,read_step_complete located,follows,Option.bind]⟩

theorem erase_indices_preserves_an_identical_authorized_trail
    {s p keys root term code path physical terminal final used}
    (read : IndexedJoint s p keys root term code path physical terminal final used) :
    JointTrail s p keys inheritedCompilerPlacement root term code path terminal final used := by
  induction read with
  | stop rigid => exact .stop trivial rigid
  | down safe indexed written _ ih =>
    exact .down trivial safe (projection_to_old_raw_hop indexed) written ih

end Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
