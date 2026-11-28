import Yulang.GeneralDeclarativeI65I74G05ReportSound487
import Yulang.GeneralDeclarativeI65I74G05ReportRepresentationBoundary487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

def g05VisitMembershipEqual488 {n : Nat} (a b : List (CandidateVisitKey485 n)) : Bool :=
  a.all (fun key => decide (key ∈ b)) && b.all (fun key => decide (key ∈ a))

theorem g05VisitMembershipEqual_is_exact488 {n : Nat} (a b : List (CandidateVisitKey485 n)) :
    g05VisitMembershipEqual488 a b = true ↔ ∀ key, key ∈ a ↔ key ∈ b := by
  simp only [g05VisitMembershipEqual488,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h key
    exact ⟨h.1 key,h.2 key⟩
  · intro h
    exact ⟨fun key => (h key).mp,fun key => (h key).mpr⟩

def g05ReportRowEquivalent488 {n : Nat} (left right : G05CandidateRow487 n) : Bool :=
  decide (left.ordinal = right.ordinal) &&
    decide (left.mark = right.mark) && g05VisitMembershipEqual488 left.observed right.observed

def g05ReportRowsEquivalent488 {n : Nat} :
    List (G05CandidateRow487 n) → List (G05CandidateRow487 n) → Bool
  | [],[] => true
  | a::rest,b::tail => g05ReportRowEquivalent488 a b && g05ReportRowsEquivalent488 rest tail
  | _,_ => false

theorem g05ReportRowsEquivalent_preserves_all_slots_and_individual_key_coverage488
    {n : Nat} {a b : List (G05CandidateRow487 n)} (eq : g05ReportRowsEquivalent488 a b = true) :
    a.length = b.length ∧
    ∀ (i : Nat) (old : G05CandidateRow487 n), a[i]? = some old →
      ∃ fresh : G05CandidateRow487 n, b[i]? = some fresh ∧ old.ordinal = fresh.ordinal ∧
        old.mark = fresh.mark ∧ ∀ key, key ∈ old.observed ↔ key ∈ fresh.observed := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [g05ReportRowsEquivalent488]
  | cons front rest ih =>
    cases b with
    | nil => simp [g05ReportRowsEquivalent488] at eq
    | cons head tail =>
      obtain ⟨localEq,remaining⟩ := Bool.and_eq_true_iff.mp eq
      obtain ⟨len,slots⟩ := ih remaining
      refine ⟨by simp [len],?_⟩
      intro i old known
      cases i with
      | zero =>
        have exact : front = old := Option.some.inj known
        subst old
        obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp localEq
        obtain ⟨ord,mark⟩ := Bool.and_eq_true_iff.mp left
        exact ⟨head,rfl,of_decide_eq_true ord,of_decide_eq_true mark,
          (g05VisitMembershipEqual_is_exact488 _ _).mp right⟩
      | succ j => exact slots j old known

theorem g05_serialization_equivalence_preserves_the_independent_full_report488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {Allowed : Nat → CandidateVisitKey485 n → Prop} {meaning : G05LocalMeaning487}
    {a b : G05Report487 n} (same : g05ReportRowsEquivalent488 a.rows b.rows = true)
    (priority : b.priority = G05PriorityOfRows487 b.rows)
    (source : G05ExactCandidateReport487 p gd pos rel coords Allowed meaning a) :
    G05ExactCandidateReport487 p gd pos rel coords Allowed meaning b := by
  obtain ⟨length,cover⟩ := g05ReportRowsEquivalent_preserves_all_slots_and_individual_key_coverage488 same
  refine ⟨priority,length.symm.trans source.2.1,?_⟩
  intro i
  obtain ⟨r,d,whereAt,sourceAt,visits,mark⟩ := source.2.2 i
  obtain ⟨fresh,atFresh,sameOrd,sameMark,member⟩ := cover i.val r whereAt
  refine ⟨fresh,d,atFresh,sameOrd ▸ sourceAt,?_,?_⟩
  · intro key
    rw [←sameOrd]
    exact (member key).symm.trans (visits key)
  · rw [←sameMark,←sameOrd]
    exact mark

def checkFlatWithEquivalentG05Tag488 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (rel : List (Fin n × Fin n))
    (coords : List (Fin n)) (permit : Nat → CandidateVisitKey485 n → Bool) (check : G05LocalChecker487) :
    Sum Flat481.FlatReport (G05Report487 n) → Sum Flat481.FlatWitness (G05FiniteWitness487 n) → Bool
  | .inl r,.inl w => Flat481.check_full_flat p r w
  | .inr r,.inr w =>
    match readG05ScopedReport487 p gd pos rel coords permit check w with
    | none => false
    | some canonical =>
      g05ReportRowsEquivalent488 canonical.rows r.rows && decide (r.priority = G05PriorityOfRows487 r.rows)
  | _,_ => false

theorem g05_equivalent_tag_preserves_original_report_soundness_without_ordered_observation_equality488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {check : G05LocalChecker487}
    {r : G05Report487 n} {w : G05FiniteWitness487 n}
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed)
    (meaning : G05LocalMeaning487) (localProtocol : G05ExactLocalProtocol487 check meaning)
    (evidence : G05LocalEvidence487)
    (modelSound : ∀ m : Model, FitsFull p.state m → ∀ i ord d v, meaning i ord d v → evidence m i ord d v)
    (accepted : checkFlatWithEquivalentG05Tag488 p gd pos rel coords permit check (.inr r) (.inr w) = true) :
    w.roots.map LiteralVisits473.Checkpoint.which = coords ∧
    G05ExactCandidateReport487 p gd pos rel coords Allowed meaning r ∧
    G05HasOriginalModelEvidence487 p gd pos rel coords Allowed evidence r := by
  cases act : readG05ScopedReport487 p gd pos rel coords permit check w with
  | none => simp [checkFlatWithEquivalentG05Tag488,act] at accepted
  | some canonical =>
    have sound := new_g05_tag_is_sound_for_exact_prior_visits_and_the_supplied_local_meaning487
      Allowed scope meaning localProtocol evidence modelSound
      (new_tag_check_succeeds_iff_it_replays_the_same_full_report_data487.mpr act)
    have compared : (g05ReportRowsEquivalent488 canonical.rows r.rows &&
        decide (r.priority = G05PriorityOfRows487 r.rows)) = true := by
      simpa only [checkFlatWithEquivalentG05Tag488,act] using accepted
    obtain ⟨equivalent,priority⟩ := Bool.and_eq_true_iff.mp compared
    have semantic := g05_serialization_equivalence_preserves_the_independent_full_report488 equivalent
      (of_decide_eq_true priority) sound.2.1
    exact ⟨sound.1,semantic,
      exact_original_g05_candidate_report_carries_evidence_for_every_fitting_model487 semantic modelSound⟩

theorem registered_arity_for_each_visible_declaration_follows_from_any_actual_scoped_original_argument488
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {Allowed : Nat → CandidateVisitKey485 n → Prop}
    (scope : G05ExactVisitInputs487 p gd pos rel coords permit Allowed) (nonempty : coords ≠ []) :
    ∀ (i : Nat) (d : GeneralDeclarations.Declaration), (visible485 p)[i]? = some d →
      d.head.length = p.old.root.demand.arguments.length := by
  intro i d got
  let seat : Fin (visible485 p).length := ⟨i,(List.getElem?_eq_some_iff.mp got).1⟩
  cases coords with
  | nil => exact False.elim (nonempty rfl)
  | cons root rest =>
    obtain ⟨input⟩ := scope.2.2.2.2 seat 0 root rfl
    have matchingDecl : input.head.orig.declaration = d := Option.some.inj (input.cell.1.symm.trans got)
    exact matchingDecl ▸ input.exactArity

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
