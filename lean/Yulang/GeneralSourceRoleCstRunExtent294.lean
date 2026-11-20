import Yulang.GeneralSourceRoleCstErrorRuns294

/-! Exact byte coverage for touching recorded token runs, conditional on
their individual intervals being non-inverted. -/
namespace Yulang.GeneralSourceRoleCstRunExtent294
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstOriginalMarks294 (Origin)
open GeneralSourceRoleCstErrorRuns294 (TokenRun Neighbors)

def size (x : Origin) : Nat := x.occurrence.extent.high - x.occurrence.extent.low

def extent : List Origin → Option Extent
  | [] => none
  | a::rest => some ⟨a.occurrence.extent.low,
      ((a::rest).getLast (by simp)).occurrence.extent.high⟩

theorem cover {row : List Origin} (h : TokenRun row) :
    (∀ x ∈ row, x.occurrence.extent.low ≤ x.occurrence.extent.high) →
    ∃ e, extent row = some e ∧ e.high = e.low + (row.map size).sum := by
  induction h with
  | singleton x =>
    intro bounds
    have b := bounds x List.mem_cons_self
    refine ⟨x.occurrence.extent,?_ ,?_⟩
    · simp [extent]
    · simp [size]
      omega
  | @cons a b rest touching tail ih =>
    intro bounds
    obtain ⟨e,located,equal⟩ := ih (fun x hx => bounds x (List.mem_cons_of_mem _ hx))
    have hstep := bounds a List.mem_cons_self
    obtain ⟨_,_,_,_,_,_,_,_,adjacent⟩ := touching
    have identity := Option.some.inj located
    have start : e.low = b.occurrence.extent.low := (congrArg Extent.low identity).symm
    have finish : e.high = ((b::rest).getLast (by simp)).occurrence.extent.high :=
      (congrArg Extent.high identity).symm
    refine ⟨⟨a.occurrence.extent.low,e.high⟩,?_,?_⟩
    · change some (⟨a.occurrence.extent.low,
        ((a::b::rest).getLast (by simp)).occurrence.extent.high⟩ : Extent) = some ⟨a.occurrence.extent.low,e.high⟩
      rw [finish]
      rfl
    · change e.high = a.occurrence.extent.low + (size a + ((b::rest).map size).sum)
      simp only [size] at equal ⊢
      omega

end Yulang.GeneralSourceRoleCstRunExtent294
