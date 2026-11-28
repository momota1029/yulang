import Yulang.GeneralDeclarativeI65I74LocatedUniquePaths477
import Yulang.GeneralDeclarativeI65I74LocatedHeadCapture476

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)

/-- A finite lookup of the captured ordinal at an already chosen
compiled path. No original authored position is inferred. -/
def exactMarkOrdinal477 {rows} (path : List QueryStep476) (out : LocatedCapture476 rows) :
    Option Nat :=
  out.marks.findIdx? (fun m => decide (m.path = path))

theorem found_ordinal_has_exact_path477
    {rows} {p : List QueryStep476} {out : LocatedCapture476 rows} {i : Nat}
    (ok : exactMarkOrdinal477 p out = some i) :
    ∃ m, out.marks[i]? = some m ∧ m.path = p := by
  obtain ⟨hi,found,_⟩ := List.findIdx?_eq_some_iff_getElem.mp ok
  let m := out.marks[i]
  exact ⟨m,List.getElem?_eq_some_iff.mpr ⟨hi,rfl⟩,of_decide_eq_true found⟩

theorem literal_ordinal_lookup_replays_every_existing_mark477
    {rows} {p : List QueryStep476} {out : LocatedCapture476 rows} {i : Nat}
    {mark : LocatedMark476 rows}
    (unique : (out.marks.map LocatedMark476.path).Nodup)
    (seen : out.marks[i]? = some mark) (address : mark.path = p) :
    exactMarkOrdinal477 p out = some i := by
  apply List.findIdx?_eq_some_iff_getElem.mpr
  obtain ⟨hi,atIndex⟩ := List.getElem?_eq_some_iff.mp seen
  refine ⟨hi,by simp [atIndex,address],?_⟩
  intro j hji b
  have hlen : j < out.marks.length := by omega
  have same : LocatedMark476.path out.marks[j] = p := of_decide_eq_true b
  have both : (out.marks.map LocatedMark476.path)[i]? = (out.marks.map LocatedMark476.path)[j]? := by
    rw [List.getElem?_map,List.getElem?_map,seen,
      List.getElem?_eq_some_iff.mpr ⟨hlen,rfl⟩]
    simp [address,same]
  have ij := unique.eq_of_getElem?_eq (by simpa using hi) both
  omega

theorem no_captured_ordinal_exactly_when_path_not_opened477
    {rows} {p : List QueryStep476} {out : LocatedCapture476 rows} :
    exactMarkOrdinal477 p out = none ↔ ∀ m ∈ out.marks, m.path ≠ p := by
  simp [exactMarkOrdinal477,List.findIdx?_eq_none_iff]

theorem actual_head_capture_has_unique_compiled_paths477
    {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w)
    {trace : LocatedCapture476 w.offered}
    (ok : readLocatedAtHead476 r = some trace) :
    (trace.marks.map LocatedMark476.path).Nodup := by
  simp only [readLocatedAtHead476] at ok
  split at ok
  · cases he : GeneralDeclarativeNestedDecode332.decode r.head.orig.code with
    | none => simp [he] at ok
    | some q =>
      have run : runLocated476 w.offered [] .actual (.variable r.head.orig.capture.lower) q.val = some trace := by simpa [he] using ok
      exact exact_path_once_in_every_structural_capture477 run
  · cases ok

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475

