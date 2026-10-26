import YulangClosure.NativeReplayCurrent

/-!
Construct the representative laws used by native merge/Replay transport from
the actual parent-pointer operations.  `find` is the native lookup loop with
an explicit proof-side fuel; the constructed decreasing rank proves a
sufficient fuel, rather than imposing a new native cutoff.  The root and rank
are ghost data.  They neither change the parent table nor select a new union
policy.  Successful birth, root linking, and path compression preserve the
certificate; rollback and complete Rust execution refinement remain separate.
-/
namespace YulangClosure.NativeRowRepresentative

structure Forest where
  size : Nat
  parent : Nat → Nat

def empty : Forest := ⟨0, id⟩

def birth (f : Forest) : Forest := ⟨f.size + 1, f.parent⟩

def write (f : Forest) (row target : Nat) : Forest :=
  ⟨f.size, fun other => if other = row then target else f.parent other⟩

/-- The out-of-bounds result of the native vector lookup is the input row. -/
def ofList (parents : List Nat) : Forest :=
  ⟨parents.length, fun row => (parents[row]?).getD row⟩

def find (f : Forest) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, row =>
      if f.parent row = row then some row else find f fuel (f.parent row)

/-- Independent local parent-pointer equations and a decreasing ghost rank.
No idempotence or absorption law is assumed. -/
structure Certificate (f : Forest) where
  root : Nat → Nat
  rank : Nat → Nat
  height : Nat
  rankBound : ∀ row, rank row ≤ height
  within : ∀ row, row < f.size → f.parent row < f.size
  outside : ∀ row, f.size ≤ row → f.parent row = row
  atRoot : ∀ row, f.parent row = row → root row = row
  nextRoot : ∀ row, root (f.parent row) = root row
  descending : ∀ row, f.parent row ≠ row → rank (f.parent row) < rank row

def emptyCertificate : Certificate empty where
  root := id
  rank := fun _ => 0
  height := 0
  rankBound := by intro row; exact Nat.le_refl _
  within := by intro row h; exact False.elim (Nat.not_lt_zero _ h)
  outside := by intros; rfl
  atRoot := by intros; rfl
  nextRoot := by intros; rfl
  descending := by intro row h; exact False.elim (h rfl)

theorem find_correct {f : Forest} (c : Certificate f) (fuel row : Nat)
    (enough : c.rank row < fuel) :
    find f fuel row = some (c.root row) ∧
      f.parent (c.root row) = c.root row ∧ c.rank (c.root row) ≤ c.rank row := by
  induction fuel generalizing row with
  | zero => omega
  | succ fuel ih =>
      by_cases fixed : f.parent row = row
      · have root := c.atRoot row fixed
        simp [find, fixed, root]
      · have smaller := c.descending row fixed
        obtain ⟨found, terminal, rank⟩ := ih (f.parent row) (by omega)
        rw [c.nextRoot row] at found terminal rank
        exact ⟨by simpa [find, fixed] using found, terminal, by omega⟩

theorem root_fixed {f : Forest} (c : Certificate f) (row : Nat) :
    f.parent (c.root row) = c.root row :=
  (find_correct c (c.rank row + 1) row (by omega)).2.1

theorem root_idempotent {f : Forest} (c : Certificate f) (row : Nat) :
    c.root (c.root row) = c.root row := c.atRoot _ (root_fixed c row)

theorem root_rank_le {f : Forest} (c : Certificate f) (row : Nat) :
    c.rank (c.root row) ≤ c.rank row :=
  (find_correct c (c.rank row + 1) row (by omega)).2.2

theorem root_rank_lt {f : Forest} (c : Certificate f) (row : Nat)
    (nonroot : f.parent row ≠ row) : c.rank (c.root row) < c.rank row := by
  have le := root_rank_le c (f.parent row)
  rw [c.nextRoot row] at le
  have lt := c.descending row nonroot
  omega

theorem find_bounded {f : Forest} (c : Certificate f) {fuel row result : Nat}
    (inside : row < f.size) (found : find f fuel row = some result) :
    result < f.size := by
  induction fuel generalizing row with
  | zero => simp [find] at found
  | succ fuel ih =>
      by_cases fixed : f.parent row = row
      · simp [find, fixed] at found
        simpa [← found] using inside
      · apply ih (c.within row inside)
        simpa [find, fixed] using found

theorem root_bounded {f : Forest} (c : Certificate f) {row : Nat}
    (inside : row < f.size) : c.root row < f.size :=
  find_bounded c inside (find_correct c (c.rank row + 1) row (by omega)).1

theorem root_outside {f : Forest} (c : Certificate f) (row : Nat)
    (outside : f.size ≤ row) : c.root row = row := c.atRoot row (c.outside row outside)

def birthCertificate {f : Forest} (c : Certificate f) : Certificate (birth f) where
  root := c.root
  rank := c.rank
  height := c.height
  rankBound := c.rankBound
  within := by
    intro row inside
    change row < f.size + 1 at inside
    change f.parent row < f.size + 1
    by_cases prior : row < f.size
    · have := c.within row prior; omega
    · rw [c.outside row (by omega)]; exact inside
  outside := by
    intro row outside
    exact c.outside row (by change f.size + 1 ≤ row at outside; omega)
  atRoot := c.atRoot
  nextRoot := c.nextRoot
  descending := c.descending

def redirect (root : Nat → Nat) (source to row : Nat) : Nat :=
  if root row = source then to else root row

def linkRank (root rank : Nat → Nat) (source to row : Nat) : Nat :=
  if root row = source then rank row + rank to + 1 else rank row

/-- Exactly the native successful write of the copy root to the parent root.
The operation retains its directed choice; it is not union by index/rank. -/
def linkCertificate {f : Forest} (c : Certificate f) (source to : Nat)
    (fromInside : source < f.size) (toInside : to < f.size)
    (fromRoot : f.parent source = source) (toRoot : f.parent to = to)
    (different : source ≠ to) : Certificate (write f source to) where
  root := redirect c.root source to
  rank := linkRank c.root c.rank source to
  height := c.height + c.height + 1
  rankBound := by
    intro row
    have a := c.rankBound row
    have b := c.rankBound to
    simp only [linkRank]
    split <;> omega
  within := by
    intro row inside
    by_cases same : row = source
    · simpa [write, same] using toInside
    · simpa [write, same] using c.within row inside
  outside := by
    intro row outside
    have differentRow : row ≠ source := by change f.size ≤ row at outside; omega
    simpa [write, differentRow] using c.outside row outside
  atRoot := by
    intro row fixed
    by_cases same : row = source
    · subst row
      have impossible : to = source := by simpa [write] using fixed
      exact False.elim (different impossible.symm)
    · have prior : f.parent row = row := by simpa [write, same] using fixed
      have root := c.atRoot row prior
      simp [redirect, root, same]
  nextRoot := by
    intro row
    by_cases same : row = source
    · subst row
      have fr := c.atRoot source fromRoot
      have tr := c.atRoot to toRoot
      simp [write, redirect, fr, tr, Ne.symm different]
    · simp [write, same, redirect, c.nextRoot row]
  descending := by
    intro row nonroot
    by_cases same : row = source
    · subst row
      have fr := c.atRoot source fromRoot
      have tr := c.atRoot to toRoot
      simp only [write, linkRank, fr, tr, ↓reduceIte, ite_eq_right (Ne.symm different)]
      omega
    · have prior : f.parent row ≠ row := by simpa [write, same] using nonroot
      have smaller := c.descending row prior
      simp only [write, same, ↓reduceIte, linkRank, c.nextRoot row]
      split <;> omega

theorem link_absorbs {f : Forest} (c : Certificate f) (source to row : Nat) :
    redirect c.root source to (c.root row) = redirect c.root source to row := by
  simp [redirect, root_idempotent c row]

def compressCertificate {f : Forest} (c : Certificate f) (row : Nat)
    (inside : row < f.size) : Certificate (write f row (c.root row)) where
  root := c.root
  rank := c.rank
  height := c.height
  rankBound := c.rankBound
  within := by
    intro other bound
    by_cases same : other = row
    · simpa [write, same] using root_bounded c inside
    · simpa [write, same] using c.within other bound
  outside := by
    intro other outside
    have different : other ≠ row := by change f.size ≤ other at outside; omega
    simpa [write, different] using c.outside other outside
  atRoot := by
    intro other fixed
    by_cases same : other = row
    · subst other; simpa [write] using fixed
    · exact c.atRoot other (by simpa [write, same] using fixed)
  nextRoot := by
    intro other
    by_cases same : other = row
    · subst other; simpa [write] using root_idempotent c row
    · simpa [write, same] using c.nextRoot other
  descending := by
    intro other nonroot
    by_cases same : other = row
    · subst other
      have distinct : c.root row ≠ row := by simpa [write] using nonroot
      have prior : f.parent row ≠ row := fun h => distinct (c.atRoot row h)
      simpa [write] using root_rank_lt c row prior
    · simpa [write, same] using c.descending other (by simpa [write, same] using nonroot)

/-- Finite executions of the original lookup loop, without a fuel parameter. -/
inductive Lookup (f : Forest) : Nat → Nat → Prop where
  | terminal (row : Nat) (fixed : f.parent row = row) : Lookup f row row
  | follow (row result : Nat) (nonroot : f.parent row ≠ row)
      (tail : Lookup f (f.parent row) result) : Lookup f row result

theorem find_lookup {f : Forest} {fuel row result : Nat}
    (found : find f fuel row = some result) : Lookup f row result := by
  induction fuel generalizing row with
  | zero => simp [find] at found
  | succ fuel ih =>
      by_cases fixed : f.parent row = row
      · simp [find, fixed] at found
        subst result
        exact .terminal row fixed
      · exact .follow row result fixed (ih (by simpa [find, fixed] using found))

theorem lookup_unique {f : Forest} {row first second : Nat}
    (left : Lookup f row first) (right : Lookup f row second) : first = second := by
  induction left with
  | terminal row fixed =>
      cases right with
      | terminal => rfl
      | follow _ _ nonroot _ => exact False.elim (nonroot fixed)
  | follow row first nonroot tail ih =>
      cases right with
      | terminal _ fixed => exact False.elim (nonroot fixed)
      | follow _ _ _ rest => exact ih rest

theorem lookup_terminates {f : Forest} (c : Certificate f) (row : Nat) :
    Lookup f row (c.root row) :=
  find_lookup (find_correct c (c.height + 1) row (by have := c.rankBound row; omega)).1

theorem lookup_result {f : Forest} (c : Certificate f) {row result : Nat}
    (execution : Lookup f row result) : result = c.root row :=
  lookup_unique execution (lookup_terminates c row)

theorem vector_birth (parents : List Nat) :
    ofList (parents ++ [parents.length]) = birth (ofList parents) := by
  unfold ofList birth
  congr 1
  · simp
  · funext row
    change ((parents ++ [parents.length])[row]?).getD row = (parents[row]?).getD row
    by_cases inside : row < parents.length
    · rw [List.getElem?_append_left inside]
    · have outside : parents.length ≤ row := by omega
      rw [List.getElem?_append_right outside, List.getElem?_eq_none outside]
      by_cases same : row = parents.length
      · simp [same]
      · have greater : 1 ≤ row - parents.length := by omega
        rw [List.getElem?_eq_none (by simpa using greater)]

theorem vector_write (parents : List Nat) (row target : Nat)
    (inside : row < parents.length) :
    ofList (parents.set row target) = write (ofList parents) row target := by
  unfold ofList write
  congr 1
  · simp
  · funext other
    by_cases same : other = row
    · subst other
      simp [List.getElem?_set_self inside]
    · simp [List.getElem?_set_ne (Ne.symm same), same]

/-- One directed root merge, after the native lookup of both input rows. -/
def merge (f : Forest) (fuel copy parent : Nat) : Option Forest := do
  if ¬ (copy < f.size ∧ parent < f.size) then none
  else
    let source ← find f fuel copy
    let target ← find f fuel parent
    pure (if source = target then f else write f source target)

/-- Path compression follows each saved old parent after updating its slot,
exactly as `compress_candidate_forests`; it does not scan the new parent. -/
def compressPath (f : Forest) : Nat → Nat → Nat → Option Forest
  | 0, _, _ => none
  | fuel + 1, row, root =>
      if f.parent row = root then some f
      else compressPath (write f row root) fuel (f.parent row) root

def compress (f : Forest) (fuel row : Nat) : Option Forest := do
  if ¬ row < f.size then none
  else
    let root ← find f fuel row
    compressPath f fuel row root

theorem merge_constructs {f : Forest} (c : Certificate f) {fuel copy parent : Nat}
    (enough : c.height < fuel) (copyInside : copy < f.size) (parentInside : parent < f.size) :
    ∃ result, merge f fuel copy parent = some result ∧
      ∃ cert : Certificate result, ∀ row, cert.root (c.root row) = cert.root row := by
  have first := (find_correct c fuel copy (by have := c.rankBound copy; omega)).1
  have second := (find_correct c fuel parent (by have := c.rankBound parent; omega)).1
  by_cases same : c.root copy = c.root parent
  · refine ⟨f, ?_, c, root_idempotent c⟩
    simp [merge, copyInside, parentInside, first, second, same]
  · let result := write f (c.root copy) (c.root parent)
    let cert := linkCertificate c (c.root copy) (c.root parent)
      (root_bounded c copyInside) (root_bounded c parentInside)
      (root_fixed c copy) (root_fixed c parent) same
    refine ⟨result, ?_, cert, ?_⟩
    · simp [merge, copyInside, parentInside, first, second, same, result]
    · intro row
      exact link_absorbs c (c.root copy) (c.root parent) row

theorem compressPath_constructs {f : Forest} (c : Certificate f) (fuel row : Nat)
    (enough : c.rank row < fuel) (inside : row < f.size) :
    ∃ result, compressPath f fuel row (c.root row) = some result ∧
      ∃ cert : Certificate result, cert.root = c.root ∧ cert.rank = c.rank := by
  induction fuel generalizing f row with
  | zero => omega
  | succ fuel ih =>
      by_cases done : f.parent row = c.root row
      · exact ⟨f, by simp [compressPath, done], c, rfl, rfl⟩
      · have nonroot : f.parent row ≠ row := by
          intro fixed
          exact done (fixed.trans (c.atRoot row fixed).symm)
        have smaller := c.descending row nonroot
        let next := compressCertificate c row inside
        obtain ⟨result, executed, cert, roots, ranks⟩ := ih next (f.parent row)
          (by change c.rank (f.parent row) < fuel; omega)
          (by exact c.within row inside)
        refine ⟨result, ?_, cert, roots, ranks⟩
        have nextRoot : next.root (f.parent row) = c.root row := c.nextRoot row
        rw [nextRoot] at executed
        simpa [compressPath, done] using executed

theorem compress_constructs {f : Forest} (c : Certificate f) {fuel row : Nat}
    (enough : c.height < fuel) (inside : row < f.size) :
    ∃ result, compress f fuel row = some result ∧
      ∃ cert : Certificate result, cert.root = c.root ∧ cert.rank = c.rank := by
  have found := (find_correct c fuel row (by have := c.rankBound row; omega)).1
  obtain ⟨result, executed, cert, roots, ranks⟩ := compressPath_constructs c fuel row
    (by have := c.rankBound row; omega) inside
  exact ⟨result, by simpa [compress, inside, found] using executed, cert, roots, ranks⟩

/-- Successful native writes. Lookup witnesses describe the actual loop;
no canonical-map, rank, or semantic-typing premise occurs in an event. -/
inductive Step : Forest → Forest → Prop where
  | birth (f : Forest) : Step f (birth f)
  | merge (f : Forest) (copy parent source target : Nat)
      (copyInside : copy < f.size) (parentInside : parent < f.size)
      (copyLookup : Lookup f copy source) (parentLookup : Lookup f parent target)
      (different : source ≠ target) : Step f (write f source target)
  | compress (f : Forest) (row root : Nat) (inside : row < f.size)
      (lookup : Lookup f row root) : Step f (write f row root)

inductive Run : Forest → Forest → Prop where
  | nil (f : Forest) : Run f f
  | snoc {first middle last : Forest} (priorRun : Run first middle)
      (lastStep : Step middle last) : Run first last

theorem certificate_unique {f : Forest} (first second : Certificate f) :
    first.root = second.root := by
  funext row
  exact lookup_unique (lookup_terminates first row) (lookup_terminates second row)

theorem step_constructs {f g : Forest} (c : Certificate f) (step : Step f g) :
    ∃ cert : Certificate g, ∀ row, cert.root (c.root row) = cert.root row := by
  cases step with
  | birth => exact ⟨birthCertificate c, root_idempotent c⟩
  | merge copy parent source target copyInside parentInside left right different =>
      have sourceEq := lookup_result c left
      have targetEq := lookup_result c right
      subst source target
      exact ⟨linkCertificate c (c.root copy) (c.root parent)
        (root_bounded c copyInside) (root_bounded c parentInside)
        (root_fixed c copy) (root_fixed c parent) different,
        link_absorbs c (c.root copy) (c.root parent)⟩
  | compress row root inside lookup =>
      have rootEq := lookup_result c lookup
      subst root
      exact ⟨compressCertificate c row inside, root_idempotent c⟩

theorem run_constructs {first last : Forest} (c : Certificate first)
    (run : Run first last) :
    ∃ cert : Certificate last, ∀ row, cert.root (c.root row) = cert.root row := by
  induction run with
  | nil => exact ⟨c, root_idempotent c⟩
  | snoc priorRun lastStep ih =>
      obtain ⟨middle, previous⟩ := ih
      obtain ⟨last, current⟩ := step_constructs middle lastStep
      refine ⟨last, ?_⟩
      intro row
      exact (current (c.root row)).symm.trans
        ((congrArg last.root (previous row)).trans (current row))

theorem generated_certificate {last : Forest} (run : Run empty last) :
    Nonempty (Certificate last) := by
  obtain ⟨cert, _⟩ := run_constructs emptyCertificate run
  exact ⟨cert⟩

theorem run_absorbs {first last : Forest} (run : Run first last)
    (before : Certificate first) (after : Certificate last) (row : Nat) :
    after.root (before.root row) = after.root row := by
  obtain ⟨constructed, absorbs⟩ := run_constructs before run
  have unique := certificate_unique constructed after
  simpa only [unique] using absorbs row

/-- The generic operand transport premise is now a consequence of the native
parent-pointer history, for the same rigid IDs/context/source/transformer. -/
theorem run_operand_transport {first last : Forest} (run : Run first last)
    (before : Certificate first) (after : Certificate last)
    (tables : NativeMergeExpansion.Effect.Tables) (key : NativeMergeExpansion.Key) :
    NativeReplayCurrent.operand tables after.root key =
      NativeMergeExpansion.Effect.renameOutcome after.root
        (NativeReplayCurrent.operand tables before.root key) :=
  NativeReplayCurrent.operand_transport tables before.root after.root
    (run_absorbs run before after) key

theorem run_current_pair_transport {first last : Forest} (run : Run first last)
    (before : Certificate first) (after : Certificate last) (key : NativeMergeExpansion.Key) :
    NativeMergeExpansion.Effect.renamePair after.root
      (NativeReplayCurrent.currentPair before.root key) =
      NativeReplayCurrent.currentPair after.root key :=
  NativeReplayCurrent.currentPair_absorb before.root after.root
    (run_absorbs run before after) key

theorem generated_transport {first last : Forest} (priorRun : Run empty first)
    (suffix : Run first last) :
    ∃ before : Certificate first, ∃ after : Certificate last,
      (∀ row, after.root (before.root row) = after.root row) ∧
      (∀ tables key, NativeReplayCurrent.operand tables after.root key =
        NativeMergeExpansion.Effect.renameOutcome after.root
          (NativeReplayCurrent.operand tables before.root key)) := by
  obtain ⟨before⟩ := generated_certificate priorRun
  obtain ⟨after, absorbs⟩ := run_constructs before suffix
  exact ⟨before, after, absorbs, run_operand_transport suffix before after⟩

end YulangClosure.NativeRowRepresentative
