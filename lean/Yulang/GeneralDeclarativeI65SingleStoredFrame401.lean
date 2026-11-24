import Yulang.GeneralDeclarativeI65B6MixedLexical401

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Body lookup_exact)

/-- Read all positive entries of the *given* completed candidate
tape. The slot is the real visible ordinal, including intervening
rigid and pending entries. This operation does not classify a query. -/
abbrev CandidateAt401 (s : State) (q : Request) :=
  Nat × (Σ row : Declaration, AuthoredCandidate s q row)

def storedCandidateEntries401 {s q rows} : CandidateTape s q rows → List (CandidateAt401 s q)
  | .nil => []
  | .next (.matched p) tail =>
    (0,⟨_,p⟩) :: (storedCandidateEntries401 tail).map fun hit => (hit.1+1,hit.2)
  | .next (.incompatible _) tail | .next (.waiting _) tail =>
    (storedCandidateEntries401 tail).map fun hit => (hit.1+1,hit.2)

theorem candidate_entries_count_exact401 {s q rows} (t : CandidateTape s q rows) :
    (storedCandidateEntries401 t).length = t.live.length := by
  induction t with
  | nil => rfl
  | next entry rest ih =>
    cases entry <;> simp [storedCandidateEntries401,CandidateTape.live,ih]

theorem original_stored_entry_is_listed401 {s q rows row} {t : CandidateTape s q rows}
    {pick : AuthoredCandidate s q row} {i} (hit : StoredAt395 t pick i) :
    (i,⟨row,pick⟩) ∈ storedCandidateEntries401 t := by
  induction hit with
  | here => exact List.mem_cons_self
  | later status _ ih =>
    have later := List.mem_map_of_mem (f := fun hit : CandidateAt401 s q => (hit.1+1,hit.2)) ih
    cases status with
    | matched p => exact List.mem_cons_of_mem _ later
    | incompatible _ => exact later
    | waiting _ => exact later

/-- In a successful single-positive tape both returned origins
identify the exact same visible position and the same source
candidate object, not just its declaration key. -/
theorem single_positive_tape_stored_head_is_unique401 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (first last : SelectedHeadOrigin395 (row := row) t) :
    first.visibleOrdinal = last.visibleOrdinal ∧ first.pick = last.pick ∧
      first.rawOrdinal = last.rawOrdinal := by
  have one : (storedCandidateEntries401 t).length = 1 := by
    rw [candidate_entries_count_exact401,only.one]; rfl
  have ha := original_stored_entry_is_listed401 first.stored
  have hb := original_stored_entry_is_listed401 last.stored
  obtain ⟨sole,has⟩ := List.length_eq_one_iff.mp one
  rw [has] at ha hb
  have same := (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm
  have i : first.visibleOrdinal = last.visibleOrdinal := congrArg Prod.fst same
  have p : (⟨row,first.pick⟩ : Σ d : Declaration, AuthoredCandidate s q d) = ⟨row,last.pick⟩ :=
    congrArg Prod.snd same
  have eq : first.pick = last.pick := eq_of_heq (Sigma.mk.inj p).2
  have raw := first.ordinal
  rw [i,last.ordinal] at raw
  exact ⟨i,eq,Option.some.inj raw.symm⟩

theorem single_positive_source_origin_is_same401 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (first last : SelectedHeadOrigin395 (row := row) t) :
    first = last := by
  obtain ⟨i,p,j⟩ := single_positive_tape_stored_head_is_unique401 only first last
  cases first
  cases last
  dsimp at i p j
  subst_vars
  rfl

/-- The observable source frame is independent of how one obtains the
single genuine cell, including arbitrary padding outside author input
names. This does not identify frames of distinct candidate tapes. -/
theorem same_tape_same_lexical_source401 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (first last : SelectedHeadOrigin395 (row := row) t) (place : Placement)
    (before after : Nat → Capture) (scope : row.Scoped) :
    let a := preoutputFrameOfOrigin399 first place before
    let b := preoutputFrameOfOrigin399 last place after
    a.ordinal = b.ordinal ∧ a.captures = b.captures ∧
      a.clauses = b.clauses ∧ ∀ body : Body, a.slots body = b.slots body := by
  rw [single_positive_source_origin_is_same401 only first last]
  exact ⟨rfl,origin_frame_capture_table_independent_outside399 last place before after,
    origin_frame_where_independent_outside399 last place before after scope,
    origin_frame_slots_independent_outside399 last place before after⟩


/-- The atlas gives one exact input for a given request/source/ordinal.
For this same tape the proof can quantify over independently
constructed outputs without losing occurrence identity. The original
placement stays fixed; we do not equate two different placements. -/
theorem same_stored_choice_has_same_mixed_equation401 {s q row}
    {t : CandidateTape s q (visible s q)} (only : TapedMatch s q t row)
    (first last : SelectedHeadOrigin395 (row := row) t) (place : Placement)
    (before after : Nat → Capture) (scope : row.Scoped)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (atlas : B6OccurrenceAtlas401 s) (i : Fin q.demand.outputs.length)
    (left : NamedMixedOutput401 atlas (preoutputFrameOfOrigin399 first place before) i)
    (right : NamedMixedOutput401 atlas (preoutputFrameOfOrigin399 last place after) i)
    (m : Model) :
    left.receipt.actualEquation m = right.receipt.actualEquation m := by
  let a := preoutputFrameOfOrigin399 first place before
  let b := preoutputFrameOfOrigin399 last place after
  obtain ⟨ord,_,_,sameSlots⟩ := same_tape_same_lexical_source401 only first last place before after scope
  have selected := checked.2 row ((visible_exact s q row).mp first.pick.inScope).1
  have la := (lookup_exact (authoredRegistry s.current).roles row selected.identified.2.2.1
    q.demand.outputs[i].name left.body).mpr left.supplied
  have lb := (lookup_exact (authoredRegistry s.current).roles row selected.identified.2.2.1
    q.demand.outputs[i].name right.body).mpr right.supplied
  have sameBody := Option.some.inj (la.symm.trans lb)
  obtain ⟨lv,wL,sL⟩ := named_mixed_output_is_fixed_equation401 left m
  obtain ⟨rv,wR,sR⟩ := named_mixed_output_is_fixed_equation401 right m
  rcases left with ⟨l,ls,lp,la',lr,lmade⟩
  rcases right with ⟨r,rs,rp,lb',rr,rmade⟩
  change l = r at sameBody
  subst r
  change a.ordinal = b.ordinal at ord
  change atlas.read q a.ordinal i l = some lp at la'
  change atlas.read q b.ordinal i l = some rp at lb'
  rw [ord] at la'
  have samePlan := Option.some.inj (la'.symm.trans lb')
  subst rp
  change evaluateMixedRhs401 (sourceRead401 m (a.slots l)) lp = some lv at sL
  change evaluateMixedRhs401 (sourceRead401 m (b.slots l)) lp = some rv at sR
  rw [sameSlots l] at sL
  have sameVal := Option.some.inj (sL.symm.trans sR)
  rw [sameVal] at wL
  exact wL.trans wR.symm

end Yulang.GeneralDeclarativeI65
