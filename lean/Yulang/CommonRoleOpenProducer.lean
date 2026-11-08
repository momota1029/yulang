import Yulang.CommonRoleOpenDescent
import Yulang.CommonRoleSettledFrontier

/-! A concrete structural producer for the dual-inspection fragment.
It neither narrows endpoints nor solves ordinary state. The driver must check
and retain generated interval obligations; this is not full open applicability. -/
namespace Yulang.CommonRoleOpenProducer
open CommonRoleSettledSyntax
open CommonRoleOutermostResolver (Frontier)
abbrev Request := CommonRoleOpenDescent.Request
abbrev Registry := CommonRoleSettledFrontier.Registry

def children (_q : Request) (d : Declaration) (lo hi : Ty) : List Request :=
  d.requirements.map fun r => ⟨r.1, r.2.instantiate lo, r.2.instantiate hi⟩

inductive Trial where
  | blocked
  | deferred
  | hit (declaration : Declaration) (lower upper : Ty)
  deriving DecidableEq, Repr

def encode (d : Declaration) : Observation → Observation → Option Trial
  | .mismatch, _ | _, .mismatch => none
  | .blocked, _ | _, .blocked => some .blocked
  | .deferred, _ | _, .deferred => some .deferred
  | .hit lo, .hit hi => some (.hit d lo hi)

def trial (role : Nat) (lo hi : Ty) (d : Declaration) : Option Trial :=
  if d.role = role then encode d (inspect d.head lo) (inspect d.head hi) else none

/-- Independent dual inspections, with no reference to the executable trial. -/
def TrialRule (role : Nat) (lo hi : Ty) (d : Declaration) (out : Option Trial) : Prop :=
  (d.role ≠ role ∧ out = none) ∨
  (d.role = role ∧ ∃ lowObs highObs,
    Inspect d.head lo lowObs ∧ Inspect d.head hi highObs ∧ encode d lowObs highObs = out)

theorem trial_exact (role : Nat) (lo hi : Ty) (d : Declaration) (out : Option Trial) :
    trial role lo hi d = out ↔ TrialRule role lo hi d out := by
  by_cases same : d.role = role
  · constructor
    · intro h
      exact Or.inr ⟨same, _, _, inspect_sound _ _, inspect_sound _ _, by simpa [trial, same] using h⟩
    · rintro (bad | ⟨_, a, b, ha, hb, h⟩)
      · exact False.elim (bad.1 same)
      · rw [trial, ite_eq_left same, inspect_complete ha, inspect_complete hb]
        exact h
  · simp [trial, TrialRule, same, eq_comm]

def scan (role : Nat) (lo hi : Ty) : List Declaration → List Trial
  | [] => []
  | d :: rest => (trial role lo hi d).toList ++ scan role lo hi rest

inductive Scan (role : Nat) (lo hi : Ty) : List Declaration → List Trial → Prop where
  | nil : Scan role lo hi [] []
  | cons : TrialRule role lo hi d out → Scan role lo hi rest results →
      Scan role lo hi (d :: rest) (out.toList ++ results)

theorem scan_sound (role : Nat) (lo hi : Ty) (ds : List Declaration) :
    Scan role lo hi ds (scan role lo hi ds) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih => exact .cons ((trial_exact ..).mp rfl) ih

theorem scan_complete (h : Scan role lo hi ds results) : scan role lo hi ds = results := by
  induction h with
  | nil => rfl
  | cons first _ ih => simp [scan, (trial_exact ..).mpr first, ih]

theorem scan_exact (role : Nat) (lo hi : Ty) (ds : List Declaration) (results : List Trial) :
    scan role lo hi ds = results ↔ Scan role lo hi ds results :=
  ⟨fun h => h ▸ scan_sound role lo hi ds, scan_complete⟩

def hits (results : List Trial) : List (Declaration × Ty × Ty) :=
  results.filterMap fun result => match result with
    | .hit d lo hi => some (d, lo, hi)
    | _ => none

/-- Candidate data for the driver; use only after the frontier selects. -/
def production (visible : List Declaration) (q : Request) : Option (Declaration × Ty × Ty) :=
  (hits (scan q.role q.lower q.upper visible)).head?

def summarize (q : Request) (results : List Trial) : Frontier Request :=
  if .blocked ∈ results then .rejected
  else if .deferred ∈ results then .pending
  else match hits results with
    | [] => .rejected
    | [(d, lo, hi)] => .selected d.key (children q d lo hi)
    | _ => .ambiguous

inductive Decision (q : Request) (results : List Trial) : Frontier Request → Prop where
  | k2 : .blocked ∈ results → Decision q results .rejected
  | pending : .blocked ∉ results → .deferred ∈ results → Decision q results .pending
  | empty : .blocked ∉ results → .deferred ∉ results → hits results = [] → Decision q results .rejected
  | selected : .blocked ∉ results → .deferred ∉ results → hits results = [(d, lo, hi)] →
      Decision q results (.selected d.key (children q d lo hi))
  | ambiguous : .blocked ∉ results → .deferred ∉ results → 2 ≤ (hits results).length →
      Decision q results .ambiguous

theorem summarize_sound (q : Request) (results : List Trial) :
    Decision q results (summarize q results) := by
  unfold summarize
  split
  · exact .k2 ‹_›
  · rename_i noBlock
    split
    · exact .pending noBlock ‹_›
    · rename_i noDefer
      cases h : hits results with
      | nil => exact .empty noBlock noDefer h
      | cons first rest =>
          cases rest with
          | nil => exact .selected noBlock noDefer h
          | cons other tail => exact .ambiguous noBlock noDefer (by simp [h])

theorem summarize_complete (h : Decision q results result) : summarize q results = result := by
  cases h with
  | k2 h => simp [summarize, h]
  | pending a b => simp [summarize, a, b]
  | empty a b c => simp [summarize, a, b, c]
  | selected a b c => simp [summarize, a, b, c]
  | ambiguous a b c =>
      simp only [summarize, a, b, ite_false]
      cases found : hits results with
      | nil => simp [found] at c
      | cons first rest =>
          cases rest with
          | nil => simp [found] at c
          | cons => rfl

def frontier (visible : List Declaration) (q : Request) : Frontier Request :=
  if q.lower = .unknown then .pending
  else if q.lower.regular then .rejected
  else summarize q (scan q.role q.lower q.upper visible)

inductive Local (visible : List Declaration) (q : Request) : Frontier Request → Prop where
  | unknown : q.lower = .unknown → Local visible q .pending
  | root_cycle : q.lower.Regular → Local visible q .rejected
  | ready : q.lower ≠ .unknown → ¬ q.lower.Regular →
      Scan q.role q.lower q.upper visible results → Decision q results result →
      Local visible q result

theorem frontier_sound (visible : List Declaration) (q : Request) : Local visible q (frontier visible q) := by
  unfold frontier
  split
  · exact .unknown ‹_›
  · rename_i known
    split
    · exact .root_cycle ((regular_exact _).mp ‹_›)
    · rename_i finite
      exact .ready known (mt (regular_exact _).mpr finite) (scan_sound ..) (summarize_sound ..)

theorem frontier_complete (h : Local visible q result) : frontier visible q = result := by
  cases h with
  | unknown h => simp [frontier, h]
  | root_cycle regular =>
      have known : q.lower ≠ Ty.unknown := by
        intro same
        have h := (regular_exact _).mpr regular
        rw [same] at h
        cases h
      simp [frontier, known, (regular_exact _).mpr regular]
  | ready known finite scanned decision =>
      simp [frontier, known, regular_false finite, scan_complete scanned, summarize_complete decision]

abbrev protocol (visible : List Declaration) : CommonRoleOutermostResolver.Protocol Request :=
  ⟨frontier visible, Local visible⟩

theorem frontier_exact (visible : List Declaration) :
    CommonRoleOutermostResolver.FrontierExact (protocol visible) := by
  intro q result
  exact ⟨fun h => h ▸ frontier_sound visible q, frontier_complete⟩

end Yulang.CommonRoleOpenProducer
