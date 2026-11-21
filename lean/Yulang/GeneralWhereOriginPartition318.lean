import Yulang.GeneralWhereOriginFreshRead318
import Yulang.GeneralWhereOriginLayout318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralWhereOriginPartition318
open GeneralWhereOriginTrace318 (Trace rawOf)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralWhereOriginEnumerate318 (enumerate includes)
open GeneralWhereOriginLayout318 (freshCells source_iff mem_fresh)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralNominalVersionedPlans231 (variables)

def existing (j : Journal rs) (p : Plan rs) : List (Cell p) :=
  (enumerate p).filter fun c => (sourceSlot (rawOf j).base c.row.target).isSome

noncomputable def fresh (j : Journal rs) (p : Plan rs) (guard : List Nat) : List (Cell p) :=
  (freshCells (rawOf j) p).filter fun c => decide
    (c.row.target ∉ journalSources j ∧ c.row.target ∉ guard)

noncomputable def allClassified (j : Journal rs) (p : Plan rs) (guard : List Nat) : Bool :=
  (enumerate p).all fun c => (sourceSlot (rawOf j).base c.row.target).isSome ||
    decide (c.row.target ∉ GeneralNominalState.sources (rawOf j) ∧
      c.row.target ∉ journalSources j ∧ c.row.target ∉ guard)

theorem existing_iff (j : Journal rs) {p : Plan rs} (c : Cell p) :
    c ∈ existing j p ↔ ∃ i, sourceSlot (rawOf j).base c.row.target = some i := by
  simp only [existing,List.mem_filter,includes c,true_and,source_iff]
  constructor
  · rintro ⟨i,eq⟩
    exact ⟨i,(sourceSlot_exact ..).mpr eq⟩
  · rintro ⟨i,eq⟩
    exact ⟨i,(sourceSlot_exact ..).mp eq⟩

theorem fresh_iff (j : Journal rs) {p : Plan rs} (c : Cell p) (guard : List Nat) :
    c ∈ fresh j p guard ↔ c.row.target ∉ GeneralNominalState.sources (rawOf j) ∧
      c.row.target ∉ journalSources j ∧ c.row.target ∉ guard := by
  simp [fresh,mem_fresh]

theorem classified_iff (j : Journal rs) (p : Plan rs) (guard : List Nat) :
    allClassified j p guard = true ↔ ∀ c : Cell p, c ∈ existing j p ++ fresh j p guard := by
  unfold allClassified
  simp only [List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq,List.mem_append,fresh_iff,
    existing_iff,source_iff]
  constructor
  · intro ready c
    exact (ready c (includes c)).elim
      (fun ⟨i,h⟩ => .inl ⟨i,(sourceSlot_exact ..).mpr h⟩) .inr
  · intro ready c _
    exact (ready c).elim (fun ⟨i,h⟩ => .inl ⟨i,(sourceSlot_exact ..).mp h⟩) .inr

/-- Finite partition of all corrected, materialized compound rows.
A pending/colliding coordinate is not silently turned into a write. -/
theorem checked_batch {j : Journal rs} (checked : (boundary rs).Checked r)
    (trace : Trace r j) (frame : Frame (Compiled r) j.mixed.core focus key p)
    (guard : List Nat) (pass : allClassified j p guard = true)
    (m : Assignment) (valid : Models j m) :
    ∃ n, Models j n ∧ Agree (journalSources j ++ guard) m n ∧
      ∀ c : Cell p, c.row.Holds (variables p n) n := by
  obtain ⟨n,old,same,solutions⟩ := GeneralWhereOriginFreshRead318.common_without_read_assumption
    checked trace frame (existing j p) (fresh j p guard) guard
    (fun c h => (existing_iff j c).mp h) (fun c h => (fresh_iff j c guard).mp h) m valid
  exact ⟨n,old,same,fun c => solutions c ((classified_iff j p guard).mp pass c)⟩

end Yulang.GeneralWhereOriginPartition318
