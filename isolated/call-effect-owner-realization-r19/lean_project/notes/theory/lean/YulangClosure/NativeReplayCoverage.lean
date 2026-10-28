import Std

/-!
Finite scheduling facts for the native replay owners.  These are statements
about physical occurrences and emitted work, not semantic subtyping.

The two replay quadrants are `candidate_context_begin_replay`'s actual loops.
The temporal scan lemmas formalize the reviewed 2026-10-13 complete Value-block
argument, applied to current owners in the companion 2026-10-26 note.
The owner scheduler covers ordinary insert-and-replay and merge-all operations.
Resumable restoration does not automatically refine that scheduler: its saved
count/live concatenated index has the checked obstruction at the end.
No claim about source reachability of that obstruction is made here.
The shifted-index observation is previously established selected behavior,
not a newly discovered solver defect or a reason to change live indexing.
-/
namespace YulangClosure.NativeReplayCoverage

def product (lower upper : List α) : List (α × α) :=
  lower.flatMap fun l => upper.map fun u => (l, u)

theorem mem_product {lower upper : List α} {l u : α} :
    (l, u) ∈ product lower upper ↔ l ∈ lower ∧ u ∈ upper := by
  simp [product]

/-- Lists run newest to oldest, as in the native linked bound incidence. -/
def replayDelta (oldLower newLower oldUpper newUpper : List α) : List (α × α) :=
  product newLower (newUpper ++ oldUpper) ++ product oldLower newUpper

/-- The first loop owns new/new; the second loop only owns old/new. -/
theorem replay_quadrants_cover (oldLower newLower oldUpper newUpper : List α)
    (l u : α) :
    (l, u) ∈ product (newLower ++ oldLower) (newUpper ++ oldUpper) ↔
      (l, u) ∈ replayDelta oldLower newLower oldUpper newUpper ∨
      (l, u) ∈ product oldLower oldUpper := by
  simp only [replayDelta, List.mem_append, mem_product]
  constructor
  · rintro ⟨hl | hl, hu | hu⟩
    · exact Or.inl (Or.inl ⟨hl, Or.inl hu⟩)
    · exact Or.inl (Or.inl ⟨hl, Or.inr hu⟩)
    · exact Or.inl (Or.inr ⟨hl, hu⟩)
    · exact Or.inr ⟨hl, hu⟩
  · rintro ((⟨hl, hu⟩ | ⟨hl, hu⟩) | ⟨hl, hu⟩)
    · exact ⟨Or.inl hl, hu⟩
    · exact ⟨Or.inr hl, Or.inl hu⟩
    · exact ⟨Or.inr hl, Or.inr hu⟩

theorem incoming_replay_covers_all (lower upper : List α) :
    replayDelta [] lower [] upper = product lower upper := by
  simp [replayDelta, product]

structure Owner (α : Type) where
  lower : List α := []
  upper : List α := []
  pending : List (α × α) := []
  completed : List (α × α) := []

/-- Only finite scheduling state, erased from runtime. -/
def Covered (s : Owner α) : Prop :=
  ∀ l, l ∈ s.lower → ∀ u, u ∈ s.upper →
    (l, u) ∈ s.pending ∨ (l, u) ∈ s.completed

inductive Action (α : Type) where
  | lower (item : α)
  | upper (item : α)
  | merge (lower upper : List α)
  | consume

def step (s : Owner α) : Action α → Owner α
  | .lower l =>
      { s with
        lower := s.lower ++ [l]
        pending := product [l] s.upper ++ s.pending }
  | .upper u =>
      { s with
        upper := s.upper ++ [u]
        pending := product s.lower [u] ++ s.pending }
  | .merge lower upper =>
      { s with
        lower := s.lower ++ lower
        upper := s.upper ++ upper
        pending := product (s.lower ++ lower) (s.upper ++ upper) ++ s.pending }
  | .consume => match s.pending with
      | [] => s
      | item :: rest => { s with pending := rest, completed := item :: s.completed }

theorem empty_covered : Covered ({} : Owner α) := by
  intro l hl
  exact False.elim (List.not_mem_nil hl)

theorem step_covered {s : Owner α} (h : Covered s) (action : Action α) :
    Covered (step s action) := by
  cases action with
  | lower item =>
      intro l hl u hu
      simp only [step, List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · rcases h l hl u hu with hp | hd
        · exact Or.inl (List.mem_append_right _ hp)
        · exact Or.inr hd
      · exact Or.inl (List.mem_append_left _ (mem_product.mpr ⟨by simp, hu⟩))
  | upper item =>
      intro l hl u hu
      simp only [step, List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · rcases h l hl u hu with hp | hd
        · exact Or.inl (List.mem_append_right _ hp)
        · exact Or.inr hd
      · exact Or.inl (List.mem_append_left _ (mem_product.mpr ⟨hl, by simp⟩))
  | merge lower upper =>
      intro l hl u hu
      exact Or.inl (List.mem_append_left _ (mem_product.mpr ⟨hl, hu⟩))
  | consume =>
      cases hp : s.pending with
      | nil => simpa [step, hp] using h
      | cons item rest =>
          simp only [step, hp]
          intro l hl u hu
          rcases h l hl u hu with pending | done
          · rw [hp] at pending
            rcases List.mem_cons.mp pending with same | tail
            · exact Or.inr (List.mem_cons.mpr (Or.inl same))
            · exact Or.inl tail
          · exact Or.inr (List.mem_cons.mpr (Or.inr done))

def run (s : Owner α) : List (Action α) → Owner α
  | [] => s
  | action :: rest => run (step s action) rest

theorem run_covered {s : Owner α} (h : Covered s) (actions : List (Action α)) :
    Covered (run s actions) := by
  induction actions generalizing s with
  | nil => exact h
  | cons action rest ih => exact ih (step_covered h action)

/-- A rejected route contributes no ghost events, including reused numeric IDs. -/
structure Route (α : Type) where
  actions : List (Action α)
  committed : Bool

def runRoutes (s : Owner α) : List (Route α) → Owner α
  | [] => s
  | route :: rest =>
      runRoutes (if route.committed then run s route.actions else s) rest

theorem committed_routes_covered {s : Owner α} (h : Covered s)
    (routes : List (Route α)) : Covered (runRoutes s routes) := by
  induction routes generalizing s with
  | nil => exact h
  | cons route rest ih =>
      apply ih
      split
      · exact run_covered h route.actions
      · exact h

/-- No saturation or semantic solution is a premise: the result follows from
the explicit append/merge/consume program, started from the empty owner. -/
theorem completed_routes_cover (routes : List (Route α))
    (finished : (runRoutes {} routes).pending = [])
    (l u : α) (hl : l ∈ (runRoutes {} routes).lower)
    (hu : u ∈ (runRoutes {} routes).upper) :
    (l, u) ∈ (runRoutes {} routes).completed := by
  rcases committed_routes_covered empty_covered routes l hl u hu with pending | done
  · rw [finished] at pending
    exact False.elim (List.not_mem_nil pending)
  · exact done

/-- A completed restoration's actual saved-count/live-concatenation schedule.
The growth functions describe physical suffix appends between child returns;
they are not a semantic preservation or saturation assumption. -/
def scan (direct exact : List α) (directGrowth exactGrowth : Nat → List α) :
    List (Option α) :=
  (List.range (direct.length + exact.length)).map fun index =>
    (direct ++ directGrowth index ++ exact ++ exactGrowth index)[index]?

theorem scan_direct (direct exact : List α) (directGrowth exactGrowth : Nat → List α)
    (x : α) (hx : x ∈ direct) : some x ∈ scan direct exact directGrowth exactGrowth := by
  obtain ⟨index, hi, value⟩ := List.mem_iff_getElem.mp hx
  apply List.mem_map.mpr
  refine ⟨index, List.mem_range.mpr (by omega), ?_⟩
  simp only [List.append_assoc]
  rw [List.getElem?_append_left hi]
  simp [hi, value]

theorem scan_exact_without_direct_growth (direct exact : List α)
    (exactGrowth : Nat → List α) (x : α) (hx : x ∈ exact) :
    some x ∈ scan direct exact (fun _ => []) exactGrowth := by
  obtain ⟨index, hi, value⟩ := List.mem_iff_getElem.mp hx
  apply List.mem_map.mpr
  refine ⟨direct.length + index, List.mem_range.mpr (by omega), ?_⟩
  simp only [List.append_nil, List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hi]
  simp [hi, value]

/-- Complete DL/DU/EL/EU block assignment, before fiber-product generation.
Each implication states membership in the actual later snapshot, not replay
coverage. The source constructor proves these from lane order and append-only
storage. Only upper restorations require a fixed opposite direct-lower prefix. -/
theorem temporal_three_case_coverage
    (lowerDirect upperDirect : Bool) (l u : α)
    (lowerAtUpperDirect lowerAtUpperExact upperAtLowerDirect upperAtLowerExact : List α)
    (lowerGrowth upperDirectGrowth upperExactGrowth : Nat → List α)
    (dl : lowerDirect = true → l ∈ lowerAtUpperDirect)
    (eldu : lowerDirect = false → upperDirect = true → u ∈ upperAtLowerDirect)
    (eleu : lowerDirect = false → upperDirect = false → l ∈ lowerAtUpperExact) :
    some l ∈ scan lowerAtUpperDirect lowerAtUpperExact (fun _ => []) lowerGrowth ∨
      some u ∈ scan upperAtLowerDirect upperAtLowerExact upperDirectGrowth upperExactGrowth := by
  cases hl : lowerDirect with
  | true =>
      exact Or.inl (scan_direct _ _ _ _ l (dl hl))
  | false =>
      cases hu : upperDirect with
      | true => exact Or.inr (scan_direct _ _ _ _ u (eldu hl hu))
      | false => exact Or.inl (scan_exact_without_direct_growth _ _ _ l (eleu hl hu))

inductive Kind where
  | value | effect
  deriving DecidableEq, Repr

inductive Endpoint where
  | row (identity : Nat)
  | rigid (identity : Nat)
  deriving DecidableEq, Repr

structure Demand where
  kind : Kind
  lower : Endpoint
  upper : Endpoint
  deriving DecidableEq, Repr

inductive Lane where
  | valueLowerRow | valueUpperRow | valueLowerAtom | valueUpperAtom
  | effectLowerRow | effectUpperRow | effectLowerAtom | effectUpperAtom
  deriving DecidableEq, Repr

/-- Both native row/row apply owners use this level branch after reflexivity.
`true` is positive/lower storage; `false` is negative/upper storage. -/
def selectRowBound (lower upper lowerLevel upperLevel : Nat) : Nat × Bool × Nat :=
  if upperLevel ≤ lowerLevel then (lower, false, upper) else (upper, true, lower)

theorem equal_level_row_bound_is_upper (lower upper level : Nat) :
    selectRowBound lower upper level level = (lower, false, upper) := by
  simp [selectRowBound]

/-- Physical lane normalization; `canonical` is supplied by the current forest.
Rigid IDs here retain their source table interpretation; no equal-label semantics
or interpretation of Allowance is defined by this function. -/
def normalize (canonical : Kind → Nat → Nat) (lane : Lane) (owner item : Nat) : Demand :=
  match lane with
  | .valueLowerRow => ⟨.value, .row (canonical .value item), .row (canonical .value owner)⟩
  | .valueUpperRow => ⟨.value, .row (canonical .value owner), .row (canonical .value item)⟩
  | .valueLowerAtom => ⟨.value, .rigid item, .row (canonical .value owner)⟩
  | .valueUpperAtom => ⟨.value, .row (canonical .value owner), .rigid item⟩
  | .effectLowerRow => ⟨.effect, .row (canonical .effect item), .row (canonical .effect owner)⟩
  | .effectUpperRow => ⟨.effect, .row (canonical .effect owner), .row (canonical .effect item)⟩
  | .effectLowerAtom => ⟨.effect, .rigid item, .row (canonical .effect owner)⟩
  | .effectUpperAtom => ⟨.effect, .row (canonical .effect owner), .rigid item⟩

structure FunctionPorts where
  argument : Endpoint
  argumentEffect : Endpoint
  resultEffect : Endpoint
  result : Endpoint

def functionChildren (lower upper : FunctionPorts) : List Demand :=
  [⟨.value, upper.argument, lower.argument⟩,
   ⟨.effect, upper.argumentEffect, lower.argumentEffect⟩,
   ⟨.effect, lower.resultEffect, upper.resultEffect⟩,
   ⟨.value, lower.result, upper.result⟩]

theorem function_children_exact (lower upper : FunctionPorts) (d : Demand) :
    d ∈ functionChildren lower upper ↔
      d = ⟨.value, upper.argument, lower.argument⟩ ∨
      d = ⟨.effect, upper.argumentEffect, lower.argumentEffect⟩ ∨
      d = ⟨.effect, lower.resultEffect, upper.resultEffect⟩ ∨
      d = ⟨.value, lower.result, upper.result⟩ := by
  simp [functionChildren]

/-- Exact saved-count/live-index projection of the two physical lanes. -/
def liveRead (direct exact : List Endpoint) (index : Nat) : Option Endpoint :=
  (direct ++ exact)[index]?

/-- An old atom can move outside the saved total count after a direct append.
This refutes a list-stability premise, not original-source soundness. -/
theorem live_concat_saved_count_misses_atom :
    let direct := [Endpoint.row 1]
    let exact := [Endpoint.rigid 0]
    let savedCount := direct.length + exact.length
    let observed := [liveRead direct exact 0,
      liveRead (direct ++ [Endpoint.row 2]) exact 1]
    savedCount = 2 ∧
      observed = [some (.row 1), some (.row 2)] ∧
      some (.rigid 0) ∉ observed := by
  decide

end YulangClosure.NativeReplayCoverage
