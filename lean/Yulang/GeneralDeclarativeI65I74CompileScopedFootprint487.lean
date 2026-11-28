import Yulang.GeneralDeclarativeI65I74DirectScopedEnumeration487
import Yulang.GeneralDeclarativeI65I74CompiledCandidateFootprint486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions)
open Producer479 (Site Trail)

def originalVisitAnchor487 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (argument : Nat) (first : Site s pos) : OriginalVisitPrefix487 n :=
  ⟨argument, first.index, [], []⟩

def originalTerminalPermissionRespectsPrefixes487 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (argument : Nat) (first : Site s pos) (permit : CandidateVisitKey485 n → Bool) : Prop :=
  ∀ v ∈ enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first,
    v.moves ≠ [] → permit (exactGeometryKey486 argument first v) = true →
    originalSuffixPermitted487 permit (originalVisitAnchor487 argument first) v.moves v.points = true

def compileScopedFootprint487 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n) (argument : Nat) (first : Site s pos)
    (permit : CandidateVisitKey485 n → Bool) :
    Option (List (CandidateVisitKey485 n) × List (CandidatePathWire485 n)) := do
  let visitRows ← enumerateDirectScopedOldSuffixes487 rel palette permit (originalNodeBudget486 first.pattern)
    (originalVisitAnchor487 argument first) first
  let selected := visitRows.filter (fun (v : GeometricVisit486 s pos) => !v.moves.isEmpty)
  let wires ← selected.mapM (computeCandidatePacket486 palette argument first)
  pure (selected.map (exactGeometryKey486 argument first), wires)

private theorem original_anchor_suffix_key487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (argument : Nat) (first : Site s pos) (v : GeometricVisit486 s pos) :
    ((originalVisitAnchor487 argument first).withSuffix v.moves v.points).key =
      exactGeometryKey486 argument first v := rfl

private theorem proper_suffix_filter_preserves_order_and_multiplicity487 {α : Type}
    (xs : List α) (pref proper old : α → Bool)
    (same : ∀ x ∈ xs, proper x = true → pref x = old x) :
    (xs.filter pref).filter proper = xs.filter (fun v => proper v && old v) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have tail := ih (fun x m => same x (List.mem_cons_of_mem _ m))
    cases h : proper a with
    | false =>
      cases h' : pref a <;> simp [h,h',tail]
    | true =>
      have e := same a (List.mem_cons_self ..) h
      cases h' : old a <;> simp [h,h',e,tail]

theorem prefix_permission_produces_exactly_the_old_selected_geometry_in_order487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {argument : Nat} {first : Site s pos} {permit : CandidateVisitKey485 n → Bool}
    {visitRows : List (GeometricVisit486 s pos)}
    (ran : enumeratePermittedOldSuffixes487 rel palette permit (originalNodeBudget486 first.pattern)
      (originalVisitAnchor487 argument first) first = some visitRows)
    (coherent : originalTerminalPermissionRespectsPrefixes487 rel palette argument first permit) :
    visitRows.filter (fun (v : GeometricVisit486 s pos) => !v.moves.isEmpty) =
      selectAuthorizedGeometries486 argument first permit
        (enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first) := by
  let base := enumerateGuardedGeometry486 rel palette (originalNodeBudget486 first.pattern) first
  let pref := fun v : GeometricVisit486 s pos =>
    originalSuffixPermitted487 permit (originalVisitAnchor487 argument first) v.moves v.points
  let proper := fun v : GeometricVisit486 s pos => !v.moves.isEmpty
  let old := fun v : GeometricVisit486 s pos => permit (exactGeometryKey486 argument first v)
  have branch : visitRows = base.filter pref :=
    successful_scoped_suffixes_are_exactly_the_ordered_original_geometry_filter487 _ _ _ ran
  rw [branch, proper_suffix_filter_preserves_order_and_multiplicity487 base pref proper old]
  · unfold selectAuthorizedGeometries486
    congr 1
    funext v
    cases a : v.moves.isEmpty <;> cases b : permit (exactGeometryKey486 argument first v) <;>
      simp [proper,old,a,b]
  · intro v inBase isProper
    have nonempty : v.moves ≠ [] := by
      intro noMoves
      simp [proper,noMoves] at isProper
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro yes
      have term := an_approved_suffix_has_its_exact_terminal_permission487 _ _ _ _ nonempty yes
      simpa only [old,original_anchor_suffix_key487] using term
    · exact coherent v inBase nonempty

theorem successful_scoped_geometry_reuses_the_identical_candidate_packets487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {argument : Nat} {first : Site s pos} {permit : CandidateVisitKey485 n → Bool}
    {visitRows : List (GeometricVisit486 s pos)}
    (ran : enumeratePermittedOldSuffixes487 rel palette permit (originalNodeBudget486 first.pattern)
      (originalVisitAnchor487 argument first) first = some visitRows)
    (coherent : originalTerminalPermissionRespectsPrefixes487 rel palette argument first permit) :
    compileScopedFootprint487 rel palette argument first permit =
      computeCandidateFootprint486 rel palette argument first permit := by
  have same := prefix_permission_produces_exactly_the_old_selected_geometry_in_order487 ran coherent
  simp only [compileScopedFootprint487,moving_prefix_checks_before_each_hop_preserves_the_exact_scoped_result487,
    ran,computeCandidateFootprint486]
  change (do
    let ws ← (visitRows.filter (fun (v : GeometricVisit486 s pos) => !v.moves.isEmpty)).mapM (computeCandidatePacket486 palette argument first)
    pure ((visitRows.filter (fun (v : GeometricVisit486 s pos) => !v.moves.isEmpty)).map (exactGeometryKey486 argument first), ws)) = _
  rw [same]

theorem complete_guarded_old_input_gives_identical_scoped_packet_computation487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {argument : Nat} {first : Site s pos} {permit : CandidateVisitKey485 n → Bool}
    (complete : CompletePalette486 s pos rel palette)
    (guard : LiteralVisits473.GuardedObservationInput s pos rel first.index)
    (coherent : originalTerminalPermissionRespectsPrefixes487 rel palette argument first permit) :
    compileScopedFootprint487 rel palette argument first permit =
      computeCandidateFootprint486 rel palette argument first permit := by
  obtain ⟨_,h⟩ := the_computed_original_palette_has_a_scoped_read_from_each_guarded_root487 complete
    (originalNodeBudget486 first.pattern) (originalVisitAnchor487 argument first) first guard
  exact successful_scoped_geometry_reuses_the_identical_candidate_packets487 h coherent

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
