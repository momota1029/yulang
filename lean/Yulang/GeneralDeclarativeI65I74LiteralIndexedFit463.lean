import Yulang.GeneralDeclarativeI65I74PreparedOriginSoundness463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
open WrittenPattern460
open WrittenPattern460.PhysicalOrigin (Pose Origin OriginalWalk)
open RoutedInlineStructural458 (ModelOpening)
open RecordTraversal455.MixedQA (MixedPath ChildAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeInspect321 (Inspects)
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)

inductive LiteralIndexedFit (s : CoreState) (m : I72.Model) (keys : Nat → KeyRead) :
    Pattern → Nat → Expr → MixedPath → List Nat → List Pose → Nat → Pattern → Bool → Prop where
  | stop : Inspects code → LiteralIndexedFit s m keys p n code [] [] [] n p false
  | down : ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) root →
      (∃ row shape, s.current.ordinary.equations[i]? = some row ∧
        GeneralDeclarativeLowerKnown321.Alias s.current.ordinary root row.left ∧
        shapeOf row.right = some shape ∧ ChildAt shape code a c next ∧
        ModelOpening s m root row shape code a c next mark) →
      WrittenPattern460.PhysicalOrigin.Origin p (writtenAddress a) front q →
      Step (keys root) (readTerm (normalize p)) (writtenAddress a) (readTerm (normalize q)) →
      LiteralIndexedFit s m keys q c next tail rows poses n endAt remaining →
      LiteralIndexedFit s m keys p root code ((a,c)::tail) (i::rows) (front ++ poses) n endAt
        (mark || remaining)

theorem coincide_hop_by_hop_in_the_same_raw_row_and_original
    {s m keys p n e path rows poses last endpoint out used}
    (written : OriginalWalk keys p n path poses endpoint)
    (fitting : IndexedSourceFit s m keys n (readTerm (normalize p)) e path rows out last used) :
    LiteralIndexedFit s m keys p n e path rows poses out endpoint used ∧
      last = readTerm (normalize endpoint) := by
  induction written generalizing e rows last out used with
  | stop =>
    cases fitting with
    | stop inspect => exact ⟨.stop inspect,rfl⟩
  | down authored writes _ ih =>
    cases fitting with
    | down safe atRow choose rest =>
      have same := written_choice_is_unique choose writes
      rw [same] at rest
      obtain ⟨valid,eq⟩ := ih rest
      exact ⟨.down safe atRow authored writes valid,eq⟩

end Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
