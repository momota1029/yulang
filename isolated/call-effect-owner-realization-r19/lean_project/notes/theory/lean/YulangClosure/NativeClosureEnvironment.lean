import Init

/-! Candidate finite native environment supplier. Arena is a chronological append
log, not a lexical-parent chain: every appended node chooses an arbitrary older
index. Dispatch data and cell addresses are retained. No value snapshot occurs. -/
namespace YulangClosure.NativeClosureEnvironment

inductive Arena (Key Dispatch : Type) where
  | root (dispatch : Dispatch)
  | append (old : Arena Key Dispatch) (parent : Nat)
      (binder : Option (Key × Nat)) (dispatch : Dispatch)

def Arena.size : Arena K D → Nat
  | .root _ => 1
  | .append old _ _ _ => old.size + 1

inductive Valid : Arena K D → Prop where
  | root (d : D) : Valid (.root d)
  | append : Valid old → parent < old.size →
      Valid (.append old parent binder dispatch)

structure Node (K D : Type) where
  parent : Option Nat
  binder : Option (K × Nat)
  dispatch : D

def nodeAt : Arena K D → Nat → Option (Node K D)
  | .root d, i => if i = 0 then some ⟨none, none, d⟩ else none
  | .append old p b d, i =>
      if i = old.size then some ⟨some p, b, d⟩ else nodeAt old i

/-- Structurally finite evaluation. Older-index references recurse into the
old arena; Valid proves that this is precisely the native decreasing parent walk. -/
def lookup (matchesKey : K → Bool) : Arena K D → Nat → Option Nat
  | .root _, _ => none
  | .append old p b _, i =>
      if i = old.size then
        match b with
        | none => lookup matchesKey old p
        | some (key, cell) =>
            if matchesKey key then some cell else lookup matchesKey old p
      else lookup matchesKey old i

theorem lookup_old (m : K → Bool) (old : Arena K D) (p i : Nat)
    (b : Option (K × Nat)) (d : D) (hi : i < old.size) :
    lookup m (.append old p b d) i = lookup m old i := by
  simp [lookup, Nat.ne_of_lt hi]

theorem nodeAt_old (old : Arena K D) (p i : Nat)
    (b : Option (K × Nat)) (d : D) (hi : i < old.size) :
    nodeAt (.append old p b d) i = nodeAt old i := by
  simp [nodeAt, Nat.ne_of_lt hi]

theorem parent_decreases {arena : Arena K D} (valid : Valid arena)
    {i : Nat} {node : Node K D} (found : nodeAt arena i = some node)
    {p : Nat} (parent : node.parent = some p) : p < i := by
  induction valid with
  | root d =>
      simp only [nodeAt] at found
      split at found
      · cases found
        cases parent
      · cases found
  | @append old q binder dispatch hv hq ih =>
      simp only [nodeAt] at found
      split at found
      · rename_i hi
        cases found
        cases parent
        simpa [hi] using hq
      · exact ih found

/-- One append checks the newest binding before its chosen parent. These
universal equations are the nearest-match recursion, including dispatch nodes. -/
theorem lookup_new (m : K → Bool) (old : Arena K D) (p : Nat)
    (b : Option (K × Nat)) (d : D) :
    lookup m (.append old p b d) old.size =
      match b with
      | none => lookup m old p
      | some (key, cell) => if m key then some cell else lookup m old p := by
  simp [lookup]

theorem dispatch_transparent (m : K → Bool) (old : Arena K D) (p : Nat) (d : D) :
    lookup m (.append old p none d) old.size = lookup m old p := by
  simp [lookup]

def lookupKey {D : Type} [DecidableEq K] (key : K) := lookup (fun k : K => decide (k = key)) (D := D)

theorem parameter_shadows [DecidableEq K] (old : Arena K D)
    (p cell : Nat) (key : K) (d : D) :
    lookupKey key (.append old p (some (key, cell)) d) old.size = some cell := by
  simp [lookupKey, lookup]

theorem parameter_preserves [DecidableEq K] (old : Arena K D)
    (p cell : Nat) (key other : K) (d : D) (hne : key ≠ other) :
    lookupKey other (.append old p (some (key, cell)) d) old.size =
      lookupKey other old p := by
  simp [lookupKey, lookup, hne]

/-- Append histories preserve every old address, including unrelated branches. -/
inductive Extends : Arena K D → Arena K D → Prop where
  | refl : Extends a a
  | step : Extends a b → p < b.size → Extends a (.append b p binder dispatch)

theorem extends_size {a b : Arena K D} (h : Extends a b) : a.size ≤ b.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ _ ih => exact Nat.le_trans ih (Nat.le_succ _)

theorem lookup_history {a b : Arena K D} (h : Extends a b)
    (m : K → Bool) (i : Nat) (hi : i < a.size) : lookup m b i = lookup m a i := by
  induction h with
  | refl => rfl
  | step h hp ih =>
      rw [lookup_old _ _ _ _ _ _ (Nat.lt_of_lt_of_le hi (extends_size h))]
      exact ih


theorem node_bound {arena : Arena K D} {i : Nat} {node : Node K D}
    (found : nodeAt arena i = some node) : i < arena.size := by
  induction arena with
  | root d =>
      simp only [nodeAt] at found
      split at found
      · rename_i hi
        subst i
        exact Nat.zero_lt_succ _
      · cases found
  | append old p b d ih =>
      simp only [nodeAt] at found
      split at found
      · rename_i hi
        subst i
        exact Nat.lt_succ_self _
      · exact Nat.lt_trans (ih found) (Nat.lt_succ_self _)

/-- One genuine native parent-walk step, evaluated in the same arena. -/
def step (matchesKey : K → Bool) (arena : Arena K D) (node : Node K D) : Option Nat :=
  let fallback := node.parent.bind (lookup matchesKey arena)
  match node.binder with
  | none => fallback
  | some (key, cell) => if matchesKey key then some cell else fallback

theorem lookup_node {arena : Arena K D} (valid : Valid arena)
    (matchesKey : K → Bool) {i : Nat} {node : Node K D}
    (found : nodeAt arena i = some node) : lookup matchesKey arena i = step matchesKey arena node := by
  induction valid with
  | root d =>
      simp only [nodeAt] at found
      split at found
      · cases found
        rfl
      · cases found
  | @append old p binder dispatch hv hp ih =>
      simp only [nodeAt] at found
      split at found
      · rename_i hi
        subst i
        cases found
        simp [lookup, step, Nat.ne_of_lt hp]
      · have hi := node_bound found
        rw [lookup_old matchesKey old p i binder dispatch hi, ih found]
        have fallback : node.parent.bind (lookup matchesKey old) =
            node.parent.bind (lookup matchesKey (.append old p binder dispatch)) := by
          cases he : node.parent with
          | none => rfl
          | some q =>
              simp only [Option.bind_some]
              exact (lookup_old matchesKey old p q binder dispatch
                (Nat.lt_trans (parent_decreases hv found he) hi)).symm
        simp only [step, fallback]

/-- Every valid address selects an actual node; this is independent of parent validity. -/
theorem node_exists (arena : Arena K D) (i : Nat) (hi : i < arena.size) :
    ∃ node, nodeAt arena i = some node := by
  induction arena with
  | root d =>
    have hz : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
    subst i
    exact ⟨⟨none, none, d⟩, rfl⟩
  | append old p b d ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
    · obtain ⟨n, hn⟩ := ih hlt
      exact ⟨n, (nodeAt_old old p i b d hlt).trans hn⟩
    · subst i
      exact ⟨⟨some p, b, d⟩, by simp [nodeAt]⟩

/-- Outer None means exhausted fuel; Some None means native lookup finished absent. -/
def walkFuel (matchesKey : K → Bool) (arena : Arena K D) : Nat → Nat → Option (Option Nat)
  | 0, _ => none
  | fuel + 1, i =>
    match nodeAt arena i with
    | none => some none
    | some node =>
      let fallback := match node.parent with
        | none => some none
        | some p => walkFuel matchesKey arena fuel p
      match node.binder with
      | none => fallback
      | some (key, cell) => if matchesKey key then some (some cell) else fallback

/-- Exact native parent walk finishes; fuel exhaustion cannot stand for absence. -/
theorem walk_complete {arena : Arena K D} (hv : Valid arena)
    (m : K → Bool) (fuel i : Nat) (hi : i < arena.size) (hf : i < fuel) :
    walkFuel m arena fuel i = some (lookup m arena i) := by
  induction fuel generalizing i with
  | zero => exact False.elim (Nat.not_lt_zero i hf)
  | succ fuel ih =>
    obtain ⟨node, hn⟩ := node_exists arena i hi
    have fallback :
        (match node.parent with
        | none => some none
        | some p => walkFuel m arena fuel p) =
        some (node.parent.bind (lookup m arena)) := by
      cases hp : node.parent with
      | none => rfl
      | some p =>
        have hpi := parent_decreases hv hn hp
        exact ih p (Nat.lt_trans hpi hi)
          (Nat.lt_of_lt_of_le hpi (Nat.le_of_lt_succ hf))
    rw [lookup_node hv m hn]
    simp only [walkFuel, hn]
    cases hb : node.binder with
    | none => simpa only [step, hb] using fallback
    | some pair =>
      rcases pair with ⟨key, cell⟩
      cases hm : m key <;> simp [step, hb, hm, fallback]

theorem bounded_lookup {arena : Arena K D} (hv : Valid arena)
    (m : K → Bool) (i : Nat) (hi : i < arena.size) :
    walkFuel m arena (i + 1) i = some (lookup m arena i) :=
  walk_complete hv m (i+1) i hi (Nat.lt_succ_self i)

/-- Native extend copies the selected parent's dispatch; with_dispatch supplies
new dispatch explicitly. Invalid source indices remain outside Valid. -/
def extendNode (old : Arena K D) (parent : Nat) (key : K) (cell : Nat)
    (parentNode : Node K D) (_found : nodeAt old parent = some parentNode) : Arena K D :=
  .append old parent (some (key, cell)) parentNode.dispatch

/-- Finite store allocation retains old cells and writes the actual received
value at the new address. Rewrites remain separate current-store inputs. -/
structure Store (V : Type) where
  size : Nat
  cell : Nat → Option V

def Store.push (store : Store V) (value : V) : Store V :=
  ⟨store.size + 1, fun i => if i = store.size then some value else store.cell i⟩

theorem push_current (store : Store V) (value : V) :
    (store.push value).cell store.size = some value := by simp [Store.push]

theorem push_old (store : Store V) (value : V) (i : Nat) (hi : i < store.size) :
    (store.push value).cell i = store.cell i := by
  simp [Store.push, Nat.ne_of_lt hi]

structure Closure (Body : Type) where
  savedEnvironment : Nat
  body : Body

def capture (environment : Nat) (body : B) : Closure B := ⟨environment, body⟩
def entryEnvironment (closure : Closure B) (_caller : Nat) := closure.savedEnvironment

theorem closure_entry (saved caller : Nat) (body : B) :
    entryEnvironment (capture saved body) caller = saved := rfl

/-- The store argument is supplied at observation time, never at capture time. -/
def observe (m : K → Bool) (arena : Arena K D) (environment : Nat)
    (store : Nat → Option V) : Option V :=
  (lookup m arena environment).bind store

theorem observe_current (m : K → Bool) (arena : Arena K D) (environment cell : Nat)
    (store : Nat → Option V) (h : lookup m arena environment = some cell) :
    observe m arena environment store = store cell := by simp [observe, h]

theorem bind_observes_received [DecidableEq K] (old : Arena K D)
    (parent : Nat) (key : K) (dispatch : D) (store : Store V) (value : V) :
    observe (fun k => decide (k = key))
      (.append old parent (some (key, store.size)) dispatch) old.size
      (store.push value).cell = some value := by
  simp [observe, lookup, Store.push]

/-- Different full identities may have equal spelling; lookup retains identity. -/
example : lookupKey (1, "x")
    (.append (.append (.root ()) 0 (some ((1, "x"), 10)) ())
      1 (some ((2, "x"), 20)) ()) 2 = some 10 := rfl

example : lookupKey (1 : Nat)
    (.append (.append (.root ()) 0 (some (1, 10)) ())
      1 (some (1, 20)) ()) 2 = some 20 := rfl

/-- An unrelated latest append is not an ancestor of the chosen saved index. -/
example : lookupKey (1 : Nat)
    (.append (.append (.root ()) 0 (some (1, 10)) ())
      0 (some (2, 20)) ()) 1 = some 10 := rfl

example : observe (fun k : Nat => decide (k = 1))
    (.append (.root ()) 0 (some (1, 7)) ()) 1
    (fun _ => (none : Option Nat)) = none := rfl

example : observe (fun k : Nat => decide (k = 1))
    (.append (.root ()) 0 (some (1, 7)) ()) 1
    (fun _ => some (42 : Nat)) = some 42 := rfl

end YulangClosure.NativeClosureEnvironment
