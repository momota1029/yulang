import Lean.Elab.Tactic.Omega

/-! Candidate source-directed RESPONSE-TEMPLATE-1 construction.
The arena is an extensional finite Vec: `size` is its length and `at` its lookup.
Appending writes exactly the old length. Payloads retain all native frame/owner/
view/handler data; nested ResumeArgument handles are opaque Bind data.
World includes current owner, control map, receiving store and allocation counters.
The machine instrumentation step counter is excluded from this projection. The
materializer returns the actual frame and post-world, including on failure.
This module does not identify runtime Unavailable with a typed language failure.
-/
namespace YulangClosure.NativeTemplateReplay

inductive Payload (P : Type) where
  | bind : P → Payload P
  | owner : P → Payload P
  | view : P → Payload P
  | forwardHandler : P → Payload P
  deriving DecidableEq

inductive Node (P : Type) where
  | hole
  | link : Payload P → Nat → Node P
  deriving DecidableEq

structure Arena (P : Type) where
  size : Nat
  «at» : Nat → Option (Node P)

variable {P W F E R : Type} {a : Arena P}

def empty : Arena P := ⟨1, fun i => if i = 0 then some .hole else none⟩
def append (a : Arena P) (p : Payload P) : Arena P :=
  ⟨a.size + 1, fun i => if i = a.size then some (.link p (a.size - 1)) else a.at i⟩
def appendAll (a : Arena P) : List (Payload P) → Arena P
  | [] => a
  | p :: ps => appendAll (append a p) ps

def capture (savedTopFirst : List (Payload P)) (containing : P) : Arena P :=
  append (appendAll empty savedTopFirst) (.owner containing)

def root (a : Arena P) := a.size - 1

/-- Stronger than acyclicity: all occupied positive indices point backwards by one. -/
def Built (a : Arena P) : Prop :=
  0 < a.size ∧ a.at 0 = some .hole ∧
  (∀ i, i + 1 < a.size → ∃ p, a.at (i + 1) = some (.link p i)) ∧
  (∀ i, a.size ≤ i → a.at i = none)

theorem empty_built : Built (empty : Arena P) := by
  constructor
  · simp [empty]
  constructor
  · simp [empty]
  constructor
  · intro i h; simp [empty] at h
  · intro i h; simp only [empty] at h ⊢; simp [show i ≠ 0 by omega]

theorem append_built (h : Built a) (p : Payload P) : Built (append a p) := by
  rcases h with ⟨hp, hz, hl, ho⟩
  constructor
  · simp [append]
  constructor
  · simp [append, show 0 ≠ a.size by omega, hz]
  constructor
  · intro i hi
    by_cases he : i + 1 = a.size
    · refine ⟨p, ?_⟩
      simp [append, he, show a.size - 1 = i by omega]
    · obtain ⟨q, hq⟩ := hl i (by simp [append] at hi; omega)
      exact ⟨q, by simp [append, he, hq]⟩
  · intro i hi
    have hg : a.size ≤ i := by simp [append] at hi; omega
    have hn : i ≠ a.size := by simp [append] at hi; omega
    simp [append, hn, ho i hg]

theorem appendAll_built (xs : List (Payload P)) (h : Built a) :
    Built (appendAll a xs) := by
  induction xs generalizing a with
  | nil => exact h
  | cons p ps ih => exact ih (append_built h p)

theorem appendAll_size (xs : List (Payload P)) (a : Arena P) :
    (appendAll a xs).size = a.size + xs.length := by
  induction xs generalizing a with
  | nil => simp [appendAll]
  | cons p ps ih => simp [appendAll, ih, append, Nat.add_assoc, Nat.add_comm]

theorem capture_built (xs : List (Payload P)) (owner : P) : Built (capture xs owner) :=
  append_built (appendAll_built xs empty_built) _

theorem capture_size (xs : List (Payload P)) (owner : P) :
    (capture xs owner).size = xs.length + 2 := by
  simp only [capture, append, appendAll_size, empty]
  omega

theorem capture_root (xs : List (Payload P)) (owner : P) :
    root (capture xs owner) = xs.length + 1 := by
  rw [root, capture_size]; omega

theorem unique_hole (h : Built a) (e : a.at i = some .hole) : i = 0 := by
  rcases h with ⟨hp, hz, hl, ho⟩
  have hi : i < a.size := by
    by_cases hn : i < a.size
    · exact hn
    · rw [ho i (by omega)] at e
      cases e
  cases i with
  | zero => rfl
  | succ n =>
    obtain ⟨p, he⟩ := hl n hi
    rw [he] at e
    cases e

theorem predecessor (h : Built a) (e : a.at i = some (.link p j)) :
    j + 1 = i ∧ j < i ∧ i < a.size := by
  rcases h with ⟨hp, hz, hl, ho⟩
  have hi : i < a.size := by
    by_cases hn : i < a.size
    · exact hn
    · rw [ho i (by omega)] at e
      cases e
  cases i with
  | zero => rw [hz] at e; cases e
  | succ n =>
    obtain ⟨q, he⟩ := hl n hi
    rw [he] at e
    have hj : n = j := by cases e; rfl
    subst j
    exact ⟨rfl, Nat.lt_succ_self _, hi⟩

/-- No identity-frame or successful-metadata assumption is imposed. -/
inductive Materialized (W F E : Type) where
  | ok : W → F → Materialized W F E
  | error : W → E → Materialized W F E

inductive Outcome (W E : Type) where
  | returned : W → Outcome W E
  | unavailable : W → E → Outcome W E

/-- `frames` and `visited` are chronological push order, i.e. native bottom-to-top.
The outer native Vec is observed as `outer ++ frames`. Hole costs one entry.
The response is an immutable parameter, never supplied to or altered by a node.
-/
inductive Replay (a : Arena P) (m : Payload P → W → Materialized W F E) :
    Nat → W → Outcome W E → Nat → List F → List (Payload P) → Prop where
  | hole (h : a.at i = some .hole) : Replay a m i w (.returned w) 1 [] []
  | error (h : a.at i = some (.link p j)) (hm : m p w = .error w' e) :
      Replay a m i w (.unavailable w' e) 1 [] [p]
  | link (h : a.at i = some (.link p j)) (hm : m p w = .ok w' f)
      (tail : Replay a m j w' out steps frames visited) :
      Replay a m i w out (steps + 1) (f :: frames) (p :: visited)

/-- A finite successful prefix retains the actual payload/frame pairs. -/
inductive Prefix (a : Arena P) (m : Payload P → W → Materialized W F E) :
    Nat → W → Nat → W → List F → List (Payload P) → Prop where
  | refl : Prefix a m i w i w [] []
  | link (h : a.at i = some (.link p j)) (hm : m p w = .ok w' f)
      (tail : Prefix a m j w' k v frames visited) :
      Prefix a m i w k v (f :: frames) (p :: visited)

theorem prefix_rank (h : Built a) (run : Prefix a m i w j v fs ps) :
    j + fs.length = i ∧ ps.length = fs.length := by
  induction run with
  | refl => exact ⟨rfl, rfl⟩
  | link he hm tail ih =>
    obtain ⟨heq, _, _⟩ := predecessor h he
    constructor
    · simp only [List.length_cons]
      rw [← Nat.add_assoc, ih.1, heq]
    · exact congrArg Nat.succ ih.2

theorem replay_bound (h : Built a) (run : Replay a m i w out n fs ps) :
    n ≤ i + 1 ∧ fs.length ≤ i ∧ ps.length ≤ i := by
  induction run with
  | hole he => exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.zero_le _, Nat.zero_le _⟩
  | error he hm =>
    obtain ⟨heq, _, _⟩ := predecessor h he
    exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.zero_le _,
      Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_of_eq heq)⟩
  | link he hm tail ih =>
    obtain ⟨heq, _, _⟩ := predecessor h he
    have hn := ih.1
    rw [heq] at hn
    exact ⟨Nat.succ_le_succ hn,
      Nat.le_trans (Nat.succ_le_succ ih.2.1) (Nat.le_of_eq heq),
      Nat.le_trans (Nat.succ_le_succ ih.2.2) (Nat.le_of_eq heq)⟩

theorem completion_exact (h : Built a)
    (run : Replay a m i w (.returned v) n fs ps) :
    n = i + 1 ∧ fs.length = i ∧ ps.length = i := by
  generalize hout : Outcome.returned v = out at run
  induction run with
  | hole he =>
    have hz := unique_hole h he
    exact ⟨congrArg Nat.succ hz.symm, hz.symm, hz.symm⟩
  | error he hm => cases hout
  | link he hm tail ih =>
    have ih := ih hout
    obtain ⟨heq, _, _⟩ := predecessor h he
    exact ⟨congrArg Nat.succ (ih.1.trans heq),
      (congrArg Nat.succ ih.2.1).trans heq,
      (congrArg Nat.succ ih.2.2).trans heq⟩

/-- Payload order read from the actual numbered arena, from root inward. -/
def inwardPayloads (a : Arena P) : Nat → List (Payload P)
  | 0 => []
  | n + 1 => match a.at (n + 1) with
    | some (.link p _) => p :: inwardPayloads a n
    | _ => []

theorem completion_order (h : Built a)
    (run : Replay a m i w (.returned v) n fs ps) :
    ps = inwardPayloads a i := by
  generalize hout : Outcome.returned v = out at run
  induction run with
  | hole he =>
    have hi := unique_hole h he
    simp [hi, inwardPayloads]
  | error he hm => cases hout
  | link he hm tail ih =>
    have ih := ih hout
    obtain ⟨heq, _, _⟩ := predecessor h he
    rw [← heq]
    simp [inwardPayloads, heq, he, ih]

theorem prefix_order (h : Built a) (run : Prefix a m i w j v fs ps) :
    inwardPayloads a i = ps ++ inwardPayloads a j := by
  induction run with
  | refl => rfl
  | link he hm tail ih =>
    obtain ⟨heq, _, _⟩ := predecessor h he
    rw [← heq]
    simp [inwardPayloads, heq, he, ih]

/-- Earlier Vec cells survive every append, including nested-handle payloads. -/
theorem append_preserves (a : Arena P) (p : Payload P) (hi : i < a.size) :
    (append a p).at i = a.at i := by
  simp [append, show i ≠ a.size by omega]

theorem inward_append_preserves (a : Arena P) (p : Payload P)
    (hn : n < a.size) : inwardPayloads (append a p) n = inwardPayloads a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [inwardPayloads, append_preserves a p hn]
    rw [ih (by omega)]

theorem append_order (h : Built a) (p : Payload P) :
    inwardPayloads (append a p) (root (append a p)) =
      p :: inwardPayloads a (root a) := by
  have hp : 0 < a.size := h.1
  have he : a.size = (a.size - 1) + 1 := by omega
  have hr : root (append a p) = a.size := by simp [root, append]
  rw [hr, he]
  simp only [inwardPayloads]
  have ha : (append a p).at (a.size - 1 + 1) =
      some (.link p (a.size - 1)) := by simp [append, ← he]
  rw [ha]
  simp only
  rw [inward_append_preserves a p (by omega)]
  rfl

theorem appendAll_order (xs : List (Payload P)) (h : Built a) :
    inwardPayloads (appendAll a xs) (root (appendAll a xs)) =
      xs.reverse ++ inwardPayloads a (root a) := by
  induction xs generalizing a with
  | nil => simp [appendAll]
  | cons p ps ih =>
    rw [appendAll, ih (append_built h p), append_order h p]
    simp [List.reverse_cons, List.append_assoc]

theorem capture_order (xs : List (Payload P)) (owner : P) :
    inwardPayloads (capture xs owner) (root (capture xs owner)) =
      .owner owner :: xs.reverse := by
  rw [capture, append_order (appendAll_built xs empty_built),
    appendAll_order xs empty_built]
  simp [root, empty, inwardPayloads]

theorem capture_completion_order (xs : List (Payload P)) (owner : P)
    (run : Replay (capture xs owner) m (root (capture xs owner)) w
      (.returned v) n fs ps) : ps = .owner owner :: xs.reverse := by
  rw [completion_order (capture_built xs owner) run, capture_order]

/-- Constructive existence: recurse on the builder-derived index, case-split
actual materialization. The error branch retains its post-world. -/
theorem replay_exists (h : Built a) (hi : i < a.size)
    (m : Payload P → W → Materialized W F E) (w : W) :
    ∃ out n fs ps, Replay a m i w out n fs ps := by
  induction i generalizing w with
  | zero => exact ⟨.returned w, 1, [], [], .hole h.2.1⟩
  | succ i ih =>
    obtain ⟨p, hp⟩ := h.2.2.1 i hi
    cases hm : m p w with
    | error v e => exact ⟨.unavailable v e, 1, [], [p], .error hp hm⟩
    | ok v f =>
      obtain ⟨out, n, fs, ps, hr⟩ := ih (by omega) v
      exact ⟨out, n + 1, f :: fs, p :: ps, .link hp hm hr⟩

/-- Direct application to every successfully constructed suffix and every use. -/
theorem capture_replay (xs : List (Payload P)) (owner : P)
    (m : Payload P → W → Materialized W F E) (w : W) :
    ∃ out n fs ps,
      Replay (capture xs owner) m (root (capture xs owner)) w out n fs ps ∧
      n ≤ xs.length + 2 ∧ fs.length ≤ xs.length + 1 := by
  have hb := capture_built xs owner
  have hi : root (capture xs owner) < (capture xs owner).size := by
    rw [capture_root, capture_size]; omega
  obtain ⟨out, n, fs, ps, hr⟩ := replay_exists hb hi m w
  obtain ⟨hn, hf, _⟩ := replay_bound hb hr
  rw [capture_root] at hn hf
  exact ⟨out, n, fs, ps, hr, by omega, hf⟩

/-- Response and outer stack projection: returned response is the supplied value;
errors retain their native error and post-world. No typed Failure interpretation. -/
def observe (response : R) (outer : List F) (out : Outcome W E) (fs : List F) :
    (W × List F) × Sum E R :=
  match out with
  | .returned w => ((w, outer ++ fs), .inr response)
  | .unavailable w e => ((w, outer ++ fs), .inl e)

theorem observe_return (r : R) (outer fs : List F) (w : W) :
    observe r outer (Outcome.returned (E := E) w) fs =
      ((w, outer ++ fs), Sum.inr r) := rfl

theorem observe_error (r : R) (outer fs : List F) (w : W) (e : E) :
    observe r outer (.unavailable w e) fs = ((w, outer ++ fs), Sum.inl e) := rfl

/-- Terminal entry states have no successor; executing restored frames is separate. -/
inductive EntryState (W E R : Type) where
  | entering : Nat → W → EntryState W E R
  | returned : W → R → EntryState W E R
  | unavailable : W → E → EntryState W E R

inductive EntryStep (a : Arena P) (m : Payload P → W → Materialized W F E)
    (response : R) : EntryState W E R → EntryState W E R → Option F → Prop where
  | hole (h : a.at i = some .hole) :
      EntryStep a m response (.entering i w) (.returned w response) none
  | link (h : a.at i = some (.link p j)) (hm : m p w = .ok v f) :
      EntryStep a m response (.entering i w) (.entering j v) (some f)
  | error (h : a.at i = some (.link p j)) (hm : m p w = .error v e) :
      EntryStep a m response (.entering i w) (.unavailable v e) none

theorem returned_no_step : ¬ EntryStep a m r (.returned w r') s f := by
  intro h; cases h

theorem unavailable_no_step : ¬ EntryStep a m r (.unavailable w e) s f := by
  intro h; cases h

/-- The finite closure of actual one-step entries, retaining chronological pushes. -/
inductive EntryTrace (a : Arena P) (m : Payload P → W → Materialized W F E)
    (response : R) : EntryState W E R → EntryState W E R → Nat → List F → Prop where
  | nil : EntryTrace a m response s s 0 []
  | cons (step : EntryStep a m response s t f)
      (tail : EntryTrace a m response t u n fs) :
      EntryTrace a m response s u (n + 1) (f.toList ++ fs)

theorem terminal_trace (stop : ∀ t f, ¬ EntryStep a m r s t f)
    (tr : EntryTrace a m r s t n fs) : t = s ∧ n = 0 ∧ fs = [] := by
  cases tr with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons step tail => exact False.elim (stop _ _ step)

def Describes (a : Arena P) (m : Payload P → W → Materialized W F E)
    (r : R) (i : Nat) (w : W) (s : EntryState W E R) (n : Nat) (fs : List F) : Prop :=
  match s with
  | .entering j v => n = fs.length ∧ ∃ ps, Prefix a m i w j v fs ps
  | .returned v r' => r' = r ∧ ∃ ps, Replay a m i w (.returned v) n fs ps
  | .unavailable v e => ∃ ps, Replay a m i w (.unavailable v e) n fs ps

/-- Universal finite-step bridge, including both terminal constructors. -/
theorem trace_describes (tr : EntryTrace a m r s t n fs) :
    ∀ i w, s = .entering i w → Describes a m r i w t n fs := by
  induction tr with
  | nil =>
    intro i w hs
    cases hs
    exact ⟨rfl, [], .refl⟩
  | @cons s mid t f k fs step tail ih =>
    intro i w hs
    cases hs
    cases step with
    | hole hh =>
      rcases terminal_trace (fun _ _ => returned_no_step) tail with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, [], .hole hh⟩
    | error hh hm =>
      rcases terminal_trace (fun _ _ => unavailable_no_step) tail with ⟨rfl, rfl, rfl⟩
      exact ⟨_, .error hh hm⟩
    | link hh hm =>
      have ht := ih _ _ rfl
      cases f with
      | entering j v =>
        obtain ⟨hn, ps, hp⟩ := ht
        exact ⟨by simp only [Option.toList_some, List.singleton_append, List.length_cons]; omega,
          _, .link hh hm hp⟩
      | returned v r' =>
        obtain ⟨hr, ps, hp⟩ := ht
        exact ⟨hr, _, .link hh hm hp⟩
      | unavailable v e =>
        obtain ⟨ps, hp⟩ := ht
        exact ⟨_, .link hh hm hp⟩

def outcomeState (r : R) : Outcome W E → EntryState W E R
  | .returned w => .returned w r
  | .unavailable w e => .unavailable w e

theorem replay_trace (run : Replay a m i w out n fs ps) (r : R) :
    EntryTrace a m r (.entering i w) (outcomeState r out) n fs := by
  induction run with
  | hole hh => exact .cons (.hole hh) .nil
  | error hh hm => exact .cons (.error hh hm) .nil
  | link hh hm tail ih => exact .cons (.link hh hm) ih

/-- Every finite actual entry prefix is bounded, regardless of materialization errors. -/
theorem trace_bound (h : Built a) (tr : EntryTrace a m r (.entering i w) t n fs) :
    n ≤ i + 1 ∧ fs.length ≤ i := by
  have ht := trace_describes tr i w rfl
  cases t with
  | entering j v =>
    obtain ⟨hn, ps, hp⟩ := ht
    have hh := prefix_rank h hp
    have hf : fs.length ≤ i := by
      rw [← hh.1]
      exact Nat.le_add_left _ _
    constructor
    · rw [hn]
      exact Nat.le_trans hf (Nat.le_succ _)
    · exact hf
  | returned v r' =>
    obtain ⟨_, ps, hp⟩ := ht
    exact ⟨(replay_bound h hp).1, (replay_bound h hp).2.1⟩
  | unavailable v e =>
    obtain ⟨ps, hp⟩ := ht
    exact ⟨(replay_bound h hp).1, (replay_bound h hp).2.1⟩

theorem capture_trace_bound (xs : List (Payload P)) (owner : P)
    (tr : EntryTrace (capture xs owner) m r (.entering (root (capture xs owner)) w) t n fs) :
    n ≤ xs.length + 2 ∧ fs.length ≤ xs.length + 1 := by
  have hh := trace_bound (capture_built xs owner) tr
  rw [capture_root] at hh
  exact hh

/-- A real finite step sequence to a terminal state is constructible for every use. -/
theorem capture_entry_exists (xs : List (Payload P)) (owner : P)
    (m : Payload P → W → Materialized W F E) (w : W) (r : R) :
    ∃ out n fs, EntryTrace (capture xs owner) m r
      (.entering (root (capture xs owner)) w) (outcomeState r out) n fs ∧
      n ≤ xs.length + 2 ∧ fs.length ≤ xs.length + 1 := by
  obtain ⟨out, n, fs, ps, hr, hn, hf⟩ := capture_replay xs owner m w
  exact ⟨out, n, fs, replay_trace hr r, hn, hf⟩

/-- Distinguishing construction equations; these are not source reachability tests. -/
example (o : P) : (capture [] o).at 1 = some (.link (.owner o) 0) := rfl
example (p o : P) : (capture [.bind p] o).at 1 = some (.link (.bind p) 0) := rfl
example (p o : P) : (capture [.bind p] o).at 2 = some (.link (.owner o) 1) := rfl
example (p o : P) : (capture [.bind p, .view p, .forwardHandler p] o).size = 5 := rfl
example (p : Payload P) : ¬ Built (Arena.mk 2 (fun _ => some (.link p 1))) := by
  intro h
  have he := h.2.1
  cases he

end YulangClosure.NativeTemplateReplay
