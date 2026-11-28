import Yulang.GeneralDeclarativeI65I74G05PreflightCompatibility489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (StepWire)
open Producer479 (Site Trail)

/-- Every actual nonempty prefix is checked at its exact key. Shape is
checked separately, so a truncated point list cannot authorize a trail. -/
def g05PrefixKeys489 {n : Nat} :
    OriginalVisitPrefix487 n → List StepWire → List (Fin n) → List (CandidateVisitKey485 n)
  | start,w::rest,i::tail =>
    let later := start.withNext w i
    later.key :: g05PrefixKeys489 later rest tail
  | _,_,_ => []

theorem independent_g05_prefix_permission_iff_length_and_exact_keys489
    {n : Nat} (Allowed : CandidateVisitKey485 n → Prop) (start : OriginalVisitPrefix487 n)
    (moves : List StepWire) (points : List (Fin n)) :
    IndependentPrefixPermission487 Allowed start moves points ↔
      moves.length = points.length ∧ ∀ key ∈ g05PrefixKeys489 start moves points, Allowed key := by
  induction moves generalizing start points with
  | nil =>
    cases points with
    | nil => exact ⟨fun _ => by simp [g05PrefixKeys489],fun _ => .empty start⟩
    | cons i rest =>
      constructor
      · intro impossible
        cases impossible
      · simp
  | cons w rest ih =>
    cases points with
    | nil =>
      constructor
      · intro impossible
        cases impossible
      · simp
    | cons i tail =>
      constructor
      · intro good
        cases good with
        | extend first later =>
          obtain ⟨same,every⟩ := (ih (start.withNext w i) tail).mp later
          refine ⟨congrArg Nat.succ same,?_⟩
          intro key mem
          simp only [g05PrefixKeys489,List.mem_cons] at mem
          rcases mem with rfl|mem
          · exact first
          · exact every key mem
      · rintro ⟨same,every⟩
        refine .extend (every _ (by simp [g05PrefixKeys489])) ((ih (start.withNext w i) tail).mpr ⟨?_,?_⟩)
        · exact Nat.succ.inj same
        · intro key mem
          exact every key (List.mem_cons_of_mem _ mem)

def G05PriorsAgreeOnOriginalTrails489 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (coords : List (Fin n))
    (A B : Nat → CandidateVisitKey485 n → Prop) : Prop :=
  ∀ (i ord : Nat) d, OriginalRosterCell485 p i (ord,d) →
    ∀ (root : Fin n) (argument : Nat), (root,argument) ∈ coords.zipIdx →
      ∀ (head : OriginalArgumentStart486 p gd pos i argument root)
        (v : GeometricVisit486 p.old.state.core pos),
        Trail p.old.state.core pos rel head.site v.moves v.points v.last v.bit →
        ∀ key ∈ g05PrefixKeys489 (originalVisitAnchor487 argument head.site) v.moves v.points,
          A ord key ↔ B ord key

theorem independent_g05_recursion_depends_on_prior_only_along_actual_original_trails489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {A B : Nat → CandidateVisitKey485 n → Prop}
    (agree : G05PriorsAgreeOnOriginalTrails489 p gd pos rel coords A B) (i : Nat) :
    IndependentScopedReturn487 p gd pos rel coords A i ↔
      IndependentScopedReturn487 p gd pos rel coords B i := by
  have transport : ∀ (A B : Nat → CandidateVisitKey485 n → Prop),
      G05PriorsAgreeOnOriginalTrails489 p gd pos rel coords A B →
      IndependentScopedReturn487 p gd pos rel coords A i →
      IndependentScopedReturn487 p gd pos rel coords B i := by
    intro X Y same
    rintro ⟨ord,d,old,root,arg,atArg,head,key,⟨v,trail,nonempty,permitted,what⟩,ending⟩
    refine ⟨ord,d,old,root,arg,atArg,head,key,⟨v,trail,nonempty,?_,what⟩,ending⟩
    obtain ⟨len,allowed⟩ := (independent_g05_prefix_permission_iff_length_and_exact_keys489
      (X ord) _ _ _).mp permitted
    exact (independent_g05_prefix_permission_iff_length_and_exact_keys489 (Y ord) _ _ _).mpr
      ⟨len,fun k used => (same i ord d old root arg atArg head v trail k used).mp (allowed k used)⟩
  exact ⟨transport A B agree,transport B A (fun i ord d old root arg atArg head v trail key used =>
    (agree i ord d old root arg atArg head v trail key used).symm)⟩

theorem two_successful_g05_preflights_agree_when_prior_differs_only_off_actual_original_trails489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {pa pb : Nat → CandidateVisitKey485 n → Bool} {a b : PreElection485}
    {A B : Nat → CandidateVisitKey485 n → Prop}
    (aRan : readG05Preflight489 p gd pos rel coords pa = some a)
    (bRan : readG05Preflight489 p gd pos rel coords pb = some b)
    (aExact : ∀ ord key, pa ord key = true ↔ A ord key)
    (bExact : ∀ ord key, pb ord key = true ↔ B ord key)
    (same : G05PriorsAgreeOnOriginalTrails489 p gd pos rel coords A B) : a = b := by
  obtain ⟨_,aBits,aMarks,aGate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 aRan A aExact
  obtain ⟨_,bBits,bMarks,bGate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 bRan B bExact
  have aAsB : G05ExactSignedRoster489 p (IndependentScopedReturn487 p gd pos rel coords B) aBits := by
    refine ⟨aMarks.1,?_⟩
    intro i
    obtain ⟨ord,d,bit,old,atBit,what⟩ := aMarks.2 i
    exact ⟨ord,d,bit,old,atBit,what.trans
      (independent_g05_recursion_depends_on_prior_only_along_actual_original_trails489 same i.val)⟩
  rw [exact_g05_signed_roster_is_unique_in_original_order489 aAsB bMarks] at aGate
  exact aGate.symm.trans bGate

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
