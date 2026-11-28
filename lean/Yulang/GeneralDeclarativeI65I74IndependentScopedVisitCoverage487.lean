import Yulang.GeneralDeclarativeI65I74CompileScopedFootprint487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (StepWire)
open Producer479 (Site Trail)

inductive IndependentPrefixPermission487 {n : Nat} (Allowed : CandidateVisitKey485 n → Prop) :
    OriginalVisitPrefix487 n → List StepWire → List (Fin n) → Prop where
  | empty (start) : IndependentPrefixPermission487 Allowed start [] []
  | extend {start w rest point points} :
      Allowed (start.withNext w point).key →
      IndependentPrefixPermission487 Allowed (start.withNext w point) rest points →
      IndependentPrefixPermission487 Allowed start (w::rest) (point::points)

theorem finite_prefix_check_is_iff_the_independent_ordered_permissions487
    {n : Nat} {permit : CandidateVisitKey485 n → Bool} {Allowed : CandidateVisitKey485 n → Prop}
    (exact : ∀ key, permit key = true ↔ Allowed key)
    (start : OriginalVisitPrefix487 n) (moves : List StepWire) (points : List (Fin n)) :
    originalSuffixPermitted487 permit start moves points = true ↔
      IndependentPrefixPermission487 Allowed start moves points := by
  induction moves generalizing start points with
  | nil =>
    cases points with
    | nil => exact ⟨fun _ => .empty start,fun _ => rfl⟩
    | cons =>
      constructor
      · intro no; cases no
      · intro no; cases no
  | cons w rest ih =>
    cases points with
    | nil =>
      constructor
      · intro no; cases no
      · intro no; cases no
    | cons i tail =>
      simp only [originalSuffixPermitted487,Bool.and_eq_true,exact,ih]
      exact ⟨fun h => .extend h.1 h.2,fun h => by cases h; exact ⟨by assumption,by assumption⟩⟩

def IndependentScopedVisit487 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (argument : Nat) (first : Site s pos)
    (Allowed : CandidateVisitKey485 n → Prop) (key : CandidateVisitKey485 n) : Prop :=
  ∃ v : GeometricVisit486 s pos,
    Trail s pos rel first v.moves v.points v.last v.bit ∧ v.moves ≠ [] ∧
    IndependentPrefixPermission487 Allowed (originalVisitAnchor487 argument first) v.moves v.points ∧
    exactGeometryKey486 argument first v = key

private theorem successful_footprint_supplies_its_exact_scoped_geometry487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {argument : Nat} {first : Site s pos} {permit : CandidateVisitKey485 n → Bool}
    {keys wires}
    (ran : compileScopedFootprint487 rel palette argument first permit = some (keys,wires)) :
    ∃ visits, enumeratePermittedOldSuffixes487 rel palette permit
      (originalNodeBudget486 first.pattern) (originalVisitAnchor487 argument first) first = some visits ∧
      keys = (visits.filter fun v => !v.moves.isEmpty).map (exactGeometryKey486 argument first) := by
  simp only [compileScopedFootprint487,moving_prefix_checks_before_each_hop_preserves_the_exact_scoped_result487] at ran
  cases read : enumeratePermittedOldSuffixes487 rel palette permit
      (originalNodeBudget486 first.pattern) (originalVisitAnchor487 argument first) first with
  | none => simp [read] at ran
  | some visits =>
    simp only [read,bind,Option.bind] at ran
    cases ws : (visits.filter fun v => !v.moves.isEmpty).mapM
        (m := Option) (computeCandidatePacket486 palette argument first) with
    | none => simp [ws] at ran
    | some wire =>
      have same := Option.some.inj (by simpa [ws] using ran :
        some ((visits.filter fun v => !v.moves.isEmpty).map (exactGeometryKey486 argument first),wire) =
          some (keys,wires))
      exact ⟨visits,rfl,(congrArg Prod.fst same).symm⟩

theorem successful_scoped_footprint_covers_exactly_independent_prefix_authorized_old_visits487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {argument : Nat} {first : Site s pos} {permit : CandidateVisitKey485 n → Bool}
    {keys wires}
    (ran : compileScopedFootprint487 rel palette argument first permit = some (keys,wires))
    (Allowed : CandidateVisitKey485 n → Prop)
    (lawful : ∀ key, permit key = true ↔ Allowed key) (key : CandidateVisitKey485 n) :
    key ∈ keys ↔ IndependentScopedVisit487 rel argument first Allowed key := by
  obtain ⟨visits,selected,keysEq⟩ := successful_footprint_supplies_its_exact_scoped_geometry487 ran
  rw [keysEq]
  constructor
  · intro member
    obtain ⟨v,inFilter,same⟩ := List.mem_map.mp member
    obtain ⟨inVisits,nonempty⟩ := List.mem_filter.mp inFilter
    have proper : v.moves ≠ [] := by
      intro missing
      simp [missing] at nonempty
    have valid := every_computed_suffix_stays_in_the_original_prior_authorized_domain487
      _ _ _ v selected inVisits
    exact ⟨v,valid.1,proper,(finite_prefix_check_is_iff_the_independent_ordered_permissions487
      lawful _ _ _).mp valid.2,same⟩
  · rintro ⟨v,trail,proper,prefixes,same⟩
    have budget := every_existing_finite_visit_stops_within_the_original_written_budget486 trail
    have fit : v.moves.length ≤ originalNodeBudget486 first.pattern := by omega
    have permitted := (finite_prefix_check_is_iff_the_independent_ordered_permissions487
      lawful _ _ _).mpr prefixes
    have inVisits : v ∈ visits := by
      cases v with
      | mk moves points last bit =>
        exact successful_scoped_enumeration_covers_every_independently_permitted_old_suffix487
          trail _ _ fit selected permitted
    have nonempty : (!v.moves.isEmpty) = true := by
      cases h : v.moves with
      | nil => exact False.elim (proper h)
      | cons => rfl
    exact List.mem_map.mpr ⟨v,List.mem_filter.mpr ⟨inVisits,nonempty⟩,same⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
