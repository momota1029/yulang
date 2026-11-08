import Yulang.CommonRoleSettledConstraints

/-! Concrete frontier production and its independent four-case local rule.
The visible registry is fixed for every descendant. All child requests retain
the same ordinary state; the later closure theorem justifies this restriction. -/
namespace Yulang.CommonRoleSettledFrontier
open CommonRoleSettledSyntax CommonRoleSettledConstraints
open CommonRoleOutermostResolver (Frontier All₂)

structure Registry where
  declarations : List Declaration
  checked : ∀ d ∈ declarations, d.check = true
  identities : (declarations.map Declaration.key).Nodup

structure Request (n : Nat) where
  role : Nat
  lower : Option Ty
  upper : Ty
  settled : ∀ t, lower = some t → upper = t
  state : State n

def Request.known (role : Nat) (t : Ty) (state : State n) : Request n :=
  ⟨role, some t, t, fun _ h => Option.some.inj h, state⟩

def Request.waiting (role : Nat) (upper : Ty) (state : State n) : Request n :=
  ⟨role, none, upper, (fun _ h => by cases h), state⟩

def children (q : Request n) (d : Declaration) (payload : Ty) : List (Request n) :=
  d.requirements.map fun r => .known r.1 (r.2.instantiate payload) q.state

inductive Trial where
  | blocked
  | deferred
  | hit (declaration : Declaration) (payload : Ty)
  deriving DecidableEq, Repr

def encode (d : Declaration) : Observation → Option Trial
  | .mismatch => none
  | .blocked => some .blocked
  | .deferred => some .deferred
  | .hit payload => some (.hit d payload)

def trial (s : State n) (role : Nat) (t : Ty) (d : Declaration) : Option Trial :=
  if d.role = role then
    if propagate s d.head t then encode d (inspect d.head t) else none
  else none

/-- Survival means satisfiable generated ordinary constraints, rigid
compatibility, and the independent graph inspection. No head assignment. -/
def TrialRule (s : State n) (role : Nat) (t : Ty) (d : Declaration)
    (out : Option Trial) : Prop :=
  (d.role ≠ role ∧ out = none) ∨
  (d.role = role ∧ ((¬ (s.Models ∧ Rigid d.head t) ∧ out = none) ∨
    (s.Models ∧ Rigid d.head t ∧ ∃ observation,
      Inspect d.head t observation ∧ encode d observation = out)))

theorem encode_exact (d : Declaration) (t : Ty) (out : Option Trial) :
    encode d (inspect d.head t) = out ↔
      ∃ observation, Inspect d.head t observation ∧ encode d observation = out := by
  constructor
  · intro h; exact ⟨_, inspect_sound _ _, h⟩
  · rintro ⟨observation, inspected, same⟩; rw [inspect_complete inspected]; exact same

theorem trial_exact (s : State n) (role : Nat) (t : Ty) (d : Declaration) (out : Option Trial) :
    trial s role t d = out ↔ TrialRule s role t d out := by
  by_cases same : d.role = role
  · by_cases ok : propagate s d.head t = true
    · have good := (propagate_exact s d.head t).mp ok
      simpa [trial, TrialRule, same, ok, good.1, good.2] using encode_exact d t out
    · have bad : ¬ (s.Models ∧ Rigid d.head t) := mt (propagate_exact s d.head t).mpr ok
      have no : ¬ (s.Models ∧ Rigid d.head t ∧ ∃ observation,
          Inspect d.head t observation ∧ encode d observation = out) := fun h => bad ⟨h.1, h.2.1⟩
      simpa [trial, TrialRule, same, Bool.eq_false_iff.mpr ok, bad, no] using
        (eq_comm : (none : Option Trial) = out ↔ out = none)
  · simp [trial, TrialRule, same, eq_comm]

def scan (s : State n) (role : Nat) (t : Ty) : List Declaration → List Trial
  | [] => []
  | d :: rest => (trial s role t d).toList ++ scan s role t rest

inductive Scan (s : State n) (role : Nat) (t : Ty) : List Declaration → List Trial → Prop where
  | nil : Scan s role t [] []
  | cons : TrialRule s role t d out → Scan s role t rest results →
      Scan s role t (d :: rest) (out.toList ++ results)

theorem scan_sound (s : State n) (role : Nat) (t : Ty) (ds : List Declaration) :
    Scan s role t ds (scan s role t ds) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih => exact .cons ((trial_exact ..).mp rfl) ih

theorem scan_complete (h : Scan s role t ds results) : scan s role t ds = results := by
  induction h with
  | nil => rfl
  | cons first _ ih => simp [scan, (trial_exact ..).mpr first, ih]

theorem scan_exact (s : State n) (role : Nat) (t : Ty) (ds : List Declaration) (results : List Trial) :
    scan s role t ds = results ↔ Scan s role t ds results :=
  ⟨fun h => h ▸ scan_sound s role t ds, scan_complete⟩

def hits (results : List Trial) : List (Declaration × Ty) :=
  results.filterMap fun result => match result with
    | .hit d t => some (d, t)
    | _ => none

def summarize (q : Request n) (results : List Trial) : Frontier (Request n) :=
  if .blocked ∈ results then .rejected
  else if .deferred ∈ results then .pending
  else match hits results with
    | [] => .rejected
    | [(d, payload)] => .selected d.key (children q d payload)
    | _ => .ambiguous

/-- The four independent cases of the design note, on the full ordered
survivor list. In particular K2 is tested before counting successful heads. -/
inductive Decision (q : Request n) (results : List Trial) : Frontier (Request n) → Prop where
  | k2 : .blocked ∈ results → Decision q results .rejected
  | pending : .blocked ∉ results → .deferred ∈ results → Decision q results .pending
  | empty : .blocked ∉ results → .deferred ∉ results → hits results = [] → Decision q results .rejected
  | selected : .blocked ∉ results → .deferred ∉ results → hits results = [(d, payload)] →
      Decision q results (.selected d.key (children q d payload))
  | ambiguous : .blocked ∉ results → .deferred ∉ results → 2 ≤ (hits results).length →
      Decision q results .ambiguous

theorem summarize_sound (q : Request n) (results : List Trial) :
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

theorem summarize_exact (q : Request n) (results : List Trial) (result : Frontier (Request n)) :
    summarize q results = result ↔ Decision q results result :=
  ⟨fun h => h ▸ summarize_sound q results, summarize_complete⟩

def frontier (visible : List Declaration) (q : Request n) : Frontier (Request n) :=
  match q.lower with
  | none => .pending
  | some t =>
      if t = .unknown then .pending
      else if t.regular then .rejected
      else summarize q (scan q.state q.role t visible)

/-- Independent Local: unknown lower, anonymous regular root, or the four
candidate/propagation cases above. It does not mention frontier or resolve. -/
inductive Local (visible : List Declaration) (q : Request n) : Frontier (Request n) → Prop where
  | absent : q.lower = none → Local visible q .pending
  | unknown : q.lower = some .unknown → Local visible q .pending
  | root_cycle : q.lower = some t → t.Regular → Local visible q .rejected
  | ready : q.lower = some t → t ≠ .unknown → ¬ t.Regular →
      Scan q.state q.role t visible results → Decision q results result → Local visible q result

theorem frontier_sound (visible : List Declaration) (q : Request n) : Local visible q (frontier visible q) := by
  unfold frontier
  cases lower : q.lower with
  | none => exact .absent lower
  | some t =>
      change Local visible q (if t = .unknown then .pending else if t.regular then .rejected else summarize q (scan q.state q.role t visible))
      split
      · rename_i unknown; subst t; exact .unknown lower
      · rename_i known
        split
        · exact .root_cycle lower ((regular_exact _).mp ‹_›)
        · rename_i finite
          exact .ready lower known (mt (regular_exact _).mpr finite)
            (scan_sound ..) (summarize_sound ..)

theorem frontier_complete (h : Local visible q result) : frontier visible q = result := by
  cases h with
  | absent h => simp [frontier, h]
  | unknown h => simp [frontier, h]
  | @root_cycle t lower regular =>
      have known : t ≠ Ty.unknown := by intro same; subst same; exact Bool.noConfusion ((regular_exact _).mpr regular)
      simp [frontier, lower, known, (regular_exact _).mpr regular]
  | ready lower known finite scanned decision =>
      simp [frontier, lower, known, regular_false finite, scan_complete scanned,
        summarize_complete decision]

abbrev protocol (visible : List Declaration) : CommonRoleOutermostResolver.Protocol (Request n) :=
  ⟨frontier visible, Local visible⟩

/-- No frontier correspondence premise. This is the concrete bridge for all
settled requests and all finite visible declaration lists. -/
theorem frontier_exact (visible : List Declaration) :
    CommonRoleOutermostResolver.FrontierExact (protocol (n := n) visible) := by
  intro q result
  exact ⟨fun h => h ▸ frontier_sound visible q, frontier_complete⟩

end Yulang.CommonRoleSettledFrontier
