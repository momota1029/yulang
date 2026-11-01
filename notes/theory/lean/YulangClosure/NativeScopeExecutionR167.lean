import YulangClosure.NativeScopeRepresentationR166

/-!
R167: finite successful source traces, on unsigned IDs after R166 encoding.
This is a source-operation abstraction, not Rust or standard-library machine-code
verification. Traces contain cursor choices and local emitted values, never
`Generated` or final encoded-field equality as execution premises.
FnMut samples retain arbitrary shared state and input-before-scope order.
Reserve/overflow failures expose no successful value. Source attribution and
external-state freshness are not inferred from finite private traces.
-/
namespace YulangClosure.NativeScopeExecutionR167

open NativeScopeTransformer NativeScopeEvaluateRefinementR165 NativeScopeRepresentationR166

inductive MergeTrace : List Nat → List Nat → List Nat → Prop where
  | leftEmpty (ys) : MergeTrace [] ys ys
  | rightEmpty (x xs) : MergeTrace (x :: xs) [] (x :: xs)
  | left {x xs y ys out} : x < y → MergeTrace xs (y :: ys) out →
      MergeTrace (x :: xs) (y :: ys) (x :: out)
  | right {x xs y ys out} : y < x → MergeTrace (x :: xs) ys out →
      MergeTrace (x :: xs) (y :: ys) (y :: out)
  | equal {x xs ys out} : MergeTrace xs ys out →
      MergeTrace (x :: xs) (x :: ys) (x :: out)

theorem mergeTrace_result {xs ys out} (trace : MergeTrace xs ys out) :
    out = unionCursor xs ys := by
  induction trace with
  | leftEmpty => simp [unionCursor]
  | rightEmpty => simp [unionCursor]
  | left h _ ih => simp [unionCursor, h, ih]
  | right h _ ih =>
      have hn : ¬ _ < _ := Nat.not_lt.mpr (Nat.le_of_lt h)
      simp [unionCursor, h, hn, ih]
  | equal _ ih => simp [unionCursor, ih]

/-- Only the mathematical contract of an unsigned sort is used. -/
def SortContract (before after : List Nat) : Prop :=
  after.Pairwise (· ≤ ·) ∧ List.Perm after before

theorem sortIds_contract (ids : List Nat) : SortContract ids (sortIds ids) := by
  refine ⟨?_, List.mergeSort_perm ids _⟩
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp; omega) ids
  exact hs.imp (fun h => of_decide_eq_true h)

theorem sortContract_unique {ids output} (contract : SortContract ids output) :
    output = sortIds ids := by
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
    contract.1 (sortIds_contract ids).1
    (contract.2.trans (sortIds_contract ids).2.symm)

/-- On sorted unsigned IDs, adjacent dedup yields a strictly ordered list
with unchanged membership. This is a std contract, not std machine code. -/
def DedupContract (before after : List Nat) : Prop :=
  after.Pairwise (· < ·) ∧ ∀ key, key ∈ after ↔ key ∈ before

theorem dedupContract_unique {ids output} (contract : DedupContract ids output) :
    output = normalize ids := by
  have outputNodup := List.nodup_iff_pairwise_ne.mpr (contract.1.imp (by omega))
  have normalNodup := List.nodup_iff_pairwise_ne.mpr ((sorted_normalize ids).imp (by omega))
  have perm : List.Perm output (normalize ids) :=
    (List.perm_ext_iff_of_nodup outputNodup normalNodup).mpr
      (fun key => (contract.2 key).trans (mem_normalize ids key).symm)
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
    (contract.1.imp (fun h => Nat.le_of_lt h))
    ((sorted_normalize ids).imp (fun h => Nat.le_of_lt h)) perm

theorem sortedCopy_contract {ids sorted output}
    (sort : SortContract ids sorted) (dedup : DedupContract sorted output) :
    output = normalize ids := by
  apply dedupContract_unique
  exact ⟨dedup.1, fun key => (dedup.2 key).trans sort.2.mem_iff⟩

def EntrySortContract (before after : List (Nat × Entry)) : Prop :=
  (keys after).Pairwise (· ≤ ·) ∧ List.Perm after before

theorem sortEntries_contract (entries : List (Nat × Entry)) :
    EntrySortContract entries (sortEntries entries) := by
  refine ⟨?_, List.mergeSort_perm entries _⟩
  have hs := List.pairwise_mergeSort
    (le := fun a b : Nat × Entry => decide (a.1 ≤ b.1))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp; omega) entries
  simpa only [keys, sortEntries, List.pairwise_map] using hs.imp (fun h => of_decide_eq_true h)

theorem unique_key (entries : List (Nat × Entry)) (distinct : (keys entries).Nodup)
    (a b : Nat × Entry) (ha : a ∈ entries) (hb : b ∈ entries) (same : a.1 = b.1) : a = b := by
  induction entries with
  | nil => simp at ha
  | cons head rest ih =>
      simp only [keys, List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp ha with hahead | harest
      · rcases List.mem_cons.mp hb with hbhead | hbrest
        · exact hahead.trans hbhead.symm
        · exact False.elim (distinct.1 (List.mem_map.mpr
            ⟨b, hbrest, same.symm.trans (congrArg Prod.fst hahead)⟩))
      · rcases List.mem_cons.mp hb with hbhead | hbrest
        · exact False.elim (distinct.1 (List.mem_map.mpr
            ⟨a, harest, same.trans (congrArg Prod.fst hbhead)⟩))
        · exact ih distinct.2 harest hbrest

theorem entrySortContract_windows {entries output}
    (contract : EntrySortContract entries output) :
    adjacentDistinct (keys output) = true ↔ (keys entries).Nodup := by
  have sortKeys : SortContract (keys entries) (keys output) :=
    ⟨contract.1, contract.2.map Prod.fst⟩
  rw [sortContract_unique sortKeys, adjacent_sort_iff_nodup]

theorem entrySortContract_success {entries output}
    (contract : EntrySortContract entries output)
    (accepted : adjacentDistinct (keys output) = true) : output = sortEntries entries := by
  have distinct := (entrySortContract_windows contract).mp accepted
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat × Entry => a.1 ≤ b.1)
  · intro a b ha hb hab hba
    exact unique_key entries distinct a b (contract.2.mem_iff.mp ha)
      ((sortEntries_contract entries).2.mem_iff.mp hb) (Nat.le_antisymm hab hba)
  · simpa only [keys, List.pairwise_map] using contract.1
  · simpa only [keys, List.pairwise_map] using (sortEntries_contract entries).1
  · exact contract.2.trans (sortEntries_contract entries).2.symm

def emit (scope : Nat) (entry : Entry) : List (Nat × Entry) :=
  if !entry.keep || !entry.missing.isEmpty then [(scope, entry)] else []

theorem emit_eq_encode (scope : Nat) (entry : Entry) :
    emit scope entry = encode [scope] (fun _ => entry) := by
  rcases entry with ⟨keep, missing⟩
  cases keep <;> cases missing <;> simp [emit, encode, identityEntry]

theorem emit_release_retained (scope : Nat) :
    emit scope ⟨false, []⟩ = [(scope, ⟨false, []⟩)] := rfl

theorem emit_neutral_omitted (scope : Nat) : emit scope identityEntry = [] := rfl

/-- The native local expression uses second.keep first and binary-search
absence on the first stamps. The search is replaced only by its mathematical
sorted-slice contract, proved in R166. -/
def sourceEntry (first second : Entry) (stamps : List Nat) : Entry :=
  ⟨second.keep && first.keep,
    unionCursor (if second.keep then first.missing else [])
      (second.missing.filter (fun tag => !(orderedSearch tag stamps)))⟩

theorem sourceEntry_model (first second : Entry) (stamps : List Nat)
    (ordered : stamps.Pairwise (· < ·)) :
    sourceEntry first second stamps = composeEntryModel first second stamps := by
  have search : ∀ tag, (!(orderedSearch tag stamps)) = decide (tag ∉ stamps) := by
    intro tag
    have hc := orderedSearch_iff tag stamps ordered
    cases h : orderedSearch tag stamps <;> simp_all
  simp only [sourceEntry, composeEntryModel, Bool.and_comm, search]

/-- Cursor suffixes are scope keys. Each emitted record reads the immutable
original keyed table at the selected ID; the consumed lemma below justifies this
read abstraction for a selected native head. -/
inductive ScopeTrace (first second : Transformer) :
    List Nat → List Nat → List (Nat × Entry) → Prop where
  | done : ScopeTrace first second [] [] []
  | leftOnly {x xs out} : ScopeTrace first second xs [] out →
      ScopeTrace first second (x :: xs) []
        (emit x (sourceEntry (first.entry x) (second.entry x) first.stamped) ++ out)
  | rightOnly {y ys out} : ScopeTrace first second [] ys out →
      ScopeTrace first second [] (y :: ys)
        (emit y (sourceEntry (first.entry y) (second.entry y) first.stamped) ++ out)
  | left {x xs y ys out} : x < y → ScopeTrace first second xs (y :: ys) out →
      ScopeTrace first second (x :: xs) (y :: ys)
        (emit x (sourceEntry (first.entry x) (second.entry x) first.stamped) ++ out)
  | right {x xs y ys out} : y < x → ScopeTrace first second (x :: xs) ys out →
      ScopeTrace first second (x :: xs) (y :: ys)
        (emit y (sourceEntry (first.entry y) (second.entry y) first.stamped) ++ out)
  | equal {x xs ys out} : ScopeTrace first second xs ys out →
      ScopeTrace first second (x :: xs) (x :: ys)
        (emit x (sourceEntry (first.entry x) (second.entry x) first.stamped) ++ out)

theorem scopeTrace_result {first second xs ys out}
    (trace : ScopeTrace first second xs ys out) (ordered : first.stamped.Pairwise (· < ·)) :
    out = encode (unionCursor xs ys)
      (fun s => composeEntryModel (first.entry s) (second.entry s) first.stamped) := by
  have push : ∀ (s : Nat) (ss : List Nat),
      encode (s :: ss) (fun s => composeEntryModel (first.entry s) (second.entry s) first.stamped) =
      emit s (composeEntryModel (first.entry s) (second.entry s) first.stamped) ++
      encode ss (fun s => composeEntryModel (first.entry s) (second.entry s) first.stamped) := by
    intro s ss
    rw [emit_eq_encode]
    simp only [encode, List.filterMap_cons, List.filterMap_nil]
    split <;> simp
  have union_nil : ∀ ids : List Nat, unionCursor ids [] = ids := by
    intro ids; cases ids <;> simp [unionCursor]
  induction trace with
  | done => simp [unionCursor, encode]
  | leftOnly _ ih => simp only [union_nil] at ih ⊢; rw [sourceEntry_model _ _ _ ordered, push, ih]
  | rightOnly _ ih => simp only [unionCursor] at ih ⊢; rw [sourceEntry_model _ _ _ ordered, push, ih]
  | left h _ ih => simp only [unionCursor, ite_eq_left h, push]; rw [sourceEntry_model _ _ _ ordered, ih]
  | right h _ ih =>
      have hn : ¬ _ < _ := Nat.not_lt.mpr (Nat.le_of_lt h)
      simp only [unionCursor, ite_eq_right hn, ite_eq_left h, push]
      rw [sourceEntry_model _ _ _ ordered, ih]
  | equal _ ih =>
      simp only [unionCursor, Nat.lt_irrefl, ↓reduceIte, push]
      rw [sourceEntry_model _ _ _ ordered, ih]

theorem entryAt_skip_consumed (consumed suffix : List (Nat × Entry)) (scope : Nat)
    (earlier : ∀ pair ∈ consumed, pair.1 < scope) :
    entryAt (consumed ++ suffix) scope = entryAt suffix scope := by
  induction consumed with
  | nil => rfl
  | cons pair rest ih =>
      have hn : pair.1 ≠ scope := Nat.ne_of_lt (earlier pair (by simp))
      simp only [List.cons_append, entryAt, hn, ↓reduceIte]
      exact ih (fun p hp => earlier p (by simp [hp]))

theorem entryAt_selected_head (consumed : List (Nat × Entry)) (scope : Nat)
    (entry : Entry) (rest : List (Nat × Entry))
    (earlier : ∀ pair ∈ consumed, pair.1 < scope) :
    entryAt (consumed ++ (scope, entry) :: rest) scope = entry := by
  rw [entryAt_skip_consumed _ _ _ earlier]
  simp [entryAt]

/-- At a cursor, all consumed entries precede the selected key, and every
pending key is at least that key. A nonmatching pending head means absence. -/
theorem entryAt_cursor_read (consumed pending : List (Nat × Entry)) (scope : Nat)
    (earlier : ∀ pair ∈ consumed, pair.1 < scope)
    (ordered : (keys pending).Pairwise (· < ·))
    (lower : ∀ pair ∈ pending, scope ≤ pair.1) :
    entryAt (consumed ++ pending) scope =
      match pending with
      | [] => identityEntry
      | (key, entry) :: _ => if key = scope then entry else identityEntry := by
  rw [entryAt_skip_consumed _ _ _ earlier]
  cases pending with
  | nil => rfl
  | cons pair rest =>
      rcases pair with ⟨key, entry⟩
      by_cases same : key = scope
      · simp [entryAt, same]
      · have strict : scope < key := Nat.lt_of_le_of_ne (lower (key, entry) (by simp)) (Ne.symm same)
        have absent : scope ∉ keys rest := by
          intro member
          have hlt := (List.pairwise_cons.mp ordered).1 scope member
          omega
        simp [entryAt, same, entryAt_absent rest scope absent]

/-- Actual remaining source records, with matching cursor advances. -/
inductive ScopeRun (stamps : List Nat) :
    List (Nat × Entry) → List (Nat × Entry) → List (Nat × Entry) → Prop where
  | done : ScopeRun stamps [] [] []
  | leftOnly {x entry xs out} : ScopeRun stamps xs [] out →
      ScopeRun stamps ((x, entry) :: xs) [] (emit x (sourceEntry entry identityEntry stamps) ++ out)
  | rightOnly {y entry ys out} : ScopeRun stamps [] ys out →
      ScopeRun stamps [] ((y, entry) :: ys) (emit y (sourceEntry identityEntry entry stamps) ++ out)
  | left {x a xs y b ys out} : x < y → ScopeRun stamps xs ((y, b) :: ys) out →
      ScopeRun stamps ((x, a) :: xs) ((y, b) :: ys) (emit x (sourceEntry a identityEntry stamps) ++ out)
  | right {x a xs y b ys out} : y < x → ScopeRun stamps ((x, a) :: xs) ys out →
      ScopeRun stamps ((x, a) :: xs) ((y, b) :: ys) (emit y (sourceEntry identityEntry b stamps) ++ out)
  | equal {x a xs b ys out} : ScopeRun stamps xs ys out →
      ScopeRun stamps ((x, a) :: xs) ((x, b) :: ys) (emit x (sourceEntry a b stamps) ++ out)

def PendingAgreement (first second : Transformer) (left right : List (Nat × Entry)) : Prop :=
  ∀ key, key ∈ keys left ∨ key ∈ keys right →
    first.entry key = entryAt left key ∧ second.entry key = entryAt right key

theorem before_head_absent (key head : Nat) (entry : Entry) (rest : List (Nat × Entry))
    (before : key < head) (ordered : (keys ((head, entry) :: rest)).Pairwise (· < ·)) :
    key ∉ keys ((head, entry) :: rest) := by
  intro present
  rcases List.mem_cons.mp present with equal | tail
  · have : key = head := equal
    omega
  · have := (List.pairwise_cons.mp ordered).1 key tail
    omega

theorem agreement_advance_left {first second x entry xs right}
    (agree : PendingAgreement first second ((x, entry) :: xs) right)
    (absent : x ∉ keys xs ∧ x ∉ keys right) : PendingAgreement first second xs right := by
  intro key present
  have old := agree key (by
    rcases present with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h)
  have different : x ≠ key := by
    intro same
    subst key
    exact present.elim absent.1 absent.2
  simpa only [entryAt, different, ↓reduceIte] using old

theorem agreement_advance_right {first second left x entry xs}
    (agree : PendingAgreement first second left ((x, entry) :: xs))
    (absent : x ∉ keys left ∧ x ∉ keys xs) : PendingAgreement first second left xs := by
  intro key present
  have old := agree key (by
    rcases present with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h))
  have different : x ≠ key := by
    intro same
    subst key
    exact present.elim absent.1 absent.2
  simpa only [entryAt, different, ↓reduceIte] using old

theorem scopeRun_trace {first second left right out}
    (run : ScopeRun first.stamped left right out) :
    (keys left).Pairwise (· < ·) → (keys right).Pairwise (· < ·) →
    PendingAgreement first second left right → ScopeTrace first second (keys left) (keys right) out := by
  induction run with
  | done => intro _ _ _; exact .done
  | @leftOnly x entry xs out _ ih =>
      intro hl hr agree
      have selected := agree x (Or.inl (by simp [keys]))
      simp only [entryAt, ↓reduceIte] at selected
      have absent : x ∉ keys xs := by
        intro present
        have := (List.pairwise_cons.mp hl).1 x present
        omega
      have tail := ih (List.pairwise_cons.mp hl).2 hr
        (agreement_advance_left agree ⟨absent, by simp [keys]⟩)
      simpa only [keys, List.map_cons, List.map_nil, selected.1, selected.2] using ScopeTrace.leftOnly (x := x) tail
  | @rightOnly y entry ys out _ ih =>
      intro hl hr agree
      have selected := agree y (Or.inr (by simp [keys]))
      simp only [entryAt, ↓reduceIte] at selected
      have absent : y ∉ keys ys := by
        intro present
        have := (List.pairwise_cons.mp hr).1 y present
        omega
      have tail := ih hl (List.pairwise_cons.mp hr).2
        (agreement_advance_right agree ⟨by simp [keys], absent⟩)
      simpa only [keys, List.map_cons, List.map_nil, selected.1, selected.2] using ScopeTrace.rightOnly (y := y) tail
  | @left x a xs y b ys out smaller _ ih =>
      intro hl hr agree
      have noRight := before_head_absent x y b ys smaller hr
      have noLeft : x ∉ keys xs := by
        intro present
        have := (List.pairwise_cons.mp hl).1 x present
        omega
      have selected := agree x (Or.inl (by simp [keys]))
      have selectedLeft : first.entry x = a := by simpa [entryAt] using selected.1
      have selectedRight : second.entry x = identityEntry :=
        selected.2.trans (entryAt_absent _ _ noRight)
      have tail := ih (List.pairwise_cons.mp hl).2 hr
        (agreement_advance_left agree ⟨noLeft, noRight⟩)
      simpa only [keys, List.map_cons, selectedLeft, selectedRight] using ScopeTrace.left smaller tail
  | @right x a xs y b ys out smaller _ ih =>
      intro hl hr agree
      have noLeft := before_head_absent y x a xs smaller hl
      have noRight : y ∉ keys ys := by
        intro present
        have := (List.pairwise_cons.mp hr).1 y present
        omega
      have selected := agree y (Or.inr (by simp [keys]))
      have selectedLeft : first.entry y = identityEntry :=
        selected.1.trans (entryAt_absent _ _ noLeft)
      have selectedRight : second.entry y = b := by simpa [entryAt] using selected.2
      have tail := ih hl (List.pairwise_cons.mp hr).2
        (agreement_advance_right agree ⟨noLeft, noRight⟩)
      simpa only [keys, List.map_cons, selectedLeft, selectedRight] using ScopeTrace.right smaller tail
  | @equal x a xs b ys out _ ih =>
      intro hl hr agree
      have noLeft : x ∉ keys xs := by
        intro present
        have := (List.pairwise_cons.mp hl).1 x present
        omega
      have noRight : x ∉ keys ys := by
        intro present
        have := (List.pairwise_cons.mp hr).1 x present
        omega
      have selected := agree x (Or.inl (by simp [keys]))
      have selectedLeft : first.entry x = a := by simpa [entryAt] using selected.1
      have selectedRight : second.entry x = b := by simpa [entryAt] using selected.2
      have tailAgree : PendingAgreement first second xs ys := by
        intro key present
        have old := agree key (by
          rcases present with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr (List.mem_cons_of_mem _ h))
        have different : x ≠ key := by
          intro same; subst key
          exact present.elim noLeft noRight
        simpa only [entryAt, different, ↓reduceIte] using old
      have tail := ih (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp hr).2 tailAgree
      simpa only [keys, List.map_cons, selectedLeft, selectedRight] using ScopeTrace.equal (x := x) tail

structure ThenTrace (first second result : Transformer) : Prop where
  stamps : MergeTrace first.stamped second.stamped result.stamped
  scopes : ScopeRun first.stamped first.scopes second.scopes result.scopes

theorem thenTrace_result {first second result} (trace : ThenTrace first second result)
    (firstOrdered : Canonical first) (secondOrdered : Canonical second) :
    result = thenModel first second := by
  cases result
  congr
  · exact mergeTrace_result trace.stamps
  · exact scopeTrace_result (scopeRun_trace trace.scopes firstOrdered.2 secondOrdered.2
      (fun _ _ => ⟨rfl, rfl⟩)) firstOrdered.1

/-- Each invocation records its state transition and returned image. -/
inductive Samples {State : Type} (call : State → Nat → State → Nat → Prop) :
    State → List Nat → State → List (Nat × Nat) → Prop where
  | nil (state) : Samples call state [] state []
  | cons {before middle after key value keys samples} : call before key middle value →
      Samples call middle keys after samples →
      Samples call before (key :: keys) after ((key, value) :: samples)

def table : List (Nat × Nat) → Nat → Nat
  | [], key => key
  | (key, value) :: rest, wanted => if key = wanted then value else table rest wanted

theorem samples_keys {State call before ids after pairs}
    (trace : @Samples State call before ids after pairs) : pairs.map Prod.fst = ids := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem table_pair (pairs : List (Nat × Nat)) (distinct : (pairs.map Prod.fst).Nodup)
    (key value : Nat) (present : (key, value) ∈ pairs) : table pairs key = value := by
  induction pairs with
  | nil => simp at present
  | cons head rest ih =>
      rcases head with ⟨k, v⟩
      simp only [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp present with heq | hrest
      · cases heq; simp [table]
      · have hn : k ≠ key := by
          intro heq
          subst k
          exact distinct.1 (List.mem_map.mpr ⟨(key, value), hrest, rfl⟩)
        simp only [table, hn, ↓reduceIte]
        exact ih distinct.2 hrest

theorem samples_values {State call before ids after pairs}
    (trace : @Samples State call before ids after pairs) (distinct : ids.Nodup) :
    ids.map (table pairs) = pairs.map Prod.snd := by
  rw [← samples_keys trace] at distinct ⊢
  simp only [List.map_map]
  exact List.map_congr_left fun pair hp => table_pair pairs distinct pair.1 pair.2 hp

/-- Binary search may choose any matching index; on distinct support its
sampled image equals table lookup. No binary-search implementation is assumed. -/
theorem sample_index_lookup {State call before ids after pairs}
    (trace : @Samples State call before ids after pairs) (distinct : ids.Nodup)
    (index key : Nat) (bound : index < ids.length) (found : ids[index] = key) :
    ∃ image, (pairs.map Prod.snd)[index]? = some image ∧ table pairs key = image := by
  have hkeys := samples_keys trace
  have pairBound : index < pairs.length := by simpa [← hkeys] using bound
  have hd : (pairs.map Prod.fst).Nodup := hkeys ▸ distinct
  have hp : pairs[index] ∈ pairs := List.getElem_mem pairBound
  have hk : pairs[index].1 = key := by
    simpa only [← hkeys, List.getElem_map] using found
  refine ⟨pairs[index].2, ?_, ?_⟩
  · simp [List.getElem?_eq_getElem pairBound]
  · rw [← hk]
    exact table_pair pairs hd _ _ hp

def BinarySearchContract (ids : List Nat) (key : Nat) (result : Option Nat) : Prop :=
  match result with
  | none => key ∉ ids
  | some index => ∃ bound : index < ids.length, ids[index] = key

theorem binarySearch_present {ids key result} (contract : BinarySearchContract ids key result)
    (present : key ∈ ids) : ∃ index, result = some index ∧ ∃ bound : index < ids.length,
      ids[index] = key := by
  cases result with
  | none => exact False.elim (contract present)
  | some index => exact ⟨index, rfl, contract⟩

/-- Input calls finish before scope calls begin; closures may share state. -/
structure RemapSampling {State : Type}
    (inputCall scopeCall : State → Nat → State → Nat → Prop)
    (transformer : Transformer) (before after : State)
    (inputs scopes : List (Nat × Nat)) where
  middle : State
  inputTrace : Samples inputCall before (inputSupport transformer) middle inputs
  scopeTrace : Samples scopeCall middle (keys transformer.scopes) after scopes

inductive Return where
  | ok (value : Transformer)
  | reserveFailure
  | overflowFailure
  | collisionFailure

/-- Recorded success/failure of the source's fallible pre-return operations.
These are abstract outcomes, not runtime receipts. -/
inductive Gate where
  | reserve (available : Bool)
  | capacity (sum : Option Nat)

def finish : List Gate → Return → Return
  | [], body => body
  | .reserve false :: _, _ => .reserveFailure
  | .reserve true :: rest, body => finish rest body
  | .capacity none :: _, _ => .overflowFailure
  | .capacity (some _) :: rest, body => finish rest body

def Gate.passed : Gate → Prop
  | .reserve available => available = true
  | .capacity sum => sum.isSome = true

theorem successful_return_boundary (gates : List Gate) (body : Return) (result : Transformer)
    (returned : finish gates body = .ok result) :
    (∀ gate ∈ gates, gate.passed) ∧ body = .ok result := by
  induction gates with
  | nil => exact ⟨by simp, returned⟩
  | cons gate rest ih =>
      cases gate with
      | reserve available =>
          cases available with
          | false => contradiction
          | true =>
              obtain ⟨all, same⟩ := ih returned
              refine ⟨?_, same⟩
              intro gate member
              rcases List.mem_cons.mp member with rfl | later
              · rfl
              · exact all gate later
      | capacity sum =>
          cases sum with
          | none => contradiction
          | some sum =>
              obtain ⟨all, same⟩ := ih returned
              refine ⟨?_, same⟩
              intro gate member
              rcases List.mem_cons.mp member with rfl | later
              · rfl
              · exact all gate later

/-- Scope images are consumed in their recorded call order. This zip does not
call a closure again; the sampling keys establish equal lengths. -/
def sampledEntries (entries : List (Nat × Entry)) (images : List Nat) (tags : Nat → Nat) :
    List (Nat × Entry) :=
  List.zipWith (fun entry image =>
    (image, ⟨entry.2.keep, sortIds (entry.2.missing.map tags)⟩)) entries images

theorem sampledEntries_table {State call before entries after pairs}
    (trace : @Samples State call before (keys entries) after pairs)
    (distinct : (keys entries).Nodup) (tags : Nat → Nat) :
    sampledEntries entries (pairs.map Prod.snd) tags =
      entries.map (fun entry => renameEntryModel entry (table pairs) tags) := by
  rw [← samples_values trace distinct]
  simp only [sampledEntries, keys, List.map_map, List.zipWith_map_right, List.zipWith_self,
    renameEntryModel, Function.comp_def]

/-- Post-sampling source operations use the table induced by actual samples. -/
def remapReturn (transformer : Transformer) (inputs scopes : List (Nat × Nat)) : Return :=
  if (normalize (inputs.map Prod.snd)).length ≠ inputs.length then .collisionFailure
  else
    let entries := sortEntries (sampledEntries transformer.scopes (scopes.map Prod.snd) (table inputs))
    if adjacentDistinct (keys entries) then
      .ok ⟨sortIds (transformer.stamped.map (table inputs)), entries⟩
    else .collisionFailure

/-- Successful source sort/dedup/window phases. Concrete std output lists are
retained; their canonical agreement is proved, not an execution premise. -/
inductive RemapSourceReturn (transformer : Transformer) (inputs scopes : List (Nat × Nat)) :
    Transformer → Prop where
  | ok {uniqueInputs stamped entries}
      (inputCopy : DedupContract (inputs.map Prod.snd) uniqueInputs)
      (inputCheck : uniqueInputs.length = inputs.length)
      (stampSort : SortContract (transformer.stamped.map (table inputs)) stamped)
      (scopeSort : EntrySortContract
        (sampledEntries transformer.scopes (scopes.map Prod.snd) (table inputs)) entries)
      (scopeCheck : adjacentDistinct (keys entries) = true) :
      RemapSourceReturn transformer inputs scopes ⟨stamped, entries⟩

theorem remapSourceReturn_result {transformer inputs scopes result}
    (trace : RemapSourceReturn transformer inputs scopes result) :
    remapReturn transformer inputs scopes = .ok result := by
  cases trace with
  | @ok uniqueInputs stamped entries inputCopy inputCheck stampSort scopeSort scopeCheck =>
      have inputCanonical := dedupContract_unique inputCopy
      have stampCanonical := sortContract_unique stampSort
      have scopeCanonical := entrySortContract_success scopeSort scopeCheck
      have hlength : (normalize (inputs.map Prod.snd)).length = inputs.length :=
        inputCanonical ▸ inputCheck
      rw [stampCanonical, scopeCanonical]
      rw [scopeCanonical] at scopeCheck
      simp [remapReturn, hlength, scopeCheck]

structure RemapTrace {State : Type} (inputCall scopeCall : State → Nat → State → Nat → Prop)
    (transformer result : Transformer) where
  before : State
  after : State
  inputs : List (Nat × Nat)
  scopes : List (Nat × Nat)
  sampling : RemapSampling inputCall scopeCall transformer before after inputs scopes
  returned : RemapSourceReturn transformer inputs scopes result

theorem remapTrace_result {State inputCall scopeCall transformer result}
    (trace : @RemapTrace State inputCall scopeCall transformer result)
    (represented : Representation transformer) :
    remapModel transformer (table trace.scopes) (table trace.inputs) = some result := by
  have inputDistinct : (inputSupport transformer).Nodup :=
    List.nodup_iff_pairwise_ne.mpr ((sorted_normalize _).imp (by omega))
  have inputValues := samples_values trace.sampling.inputTrace inputDistinct
  have inputKeys := samples_keys trace.sampling.inputTrace
  have inputLength : trace.inputs.length = (inputSupport transformer).length := by
    simpa using congrArg List.length inputKeys
  have returned := remapSourceReturn_result trace.returned
  unfold remapReturn at returned
  rw [sampledEntries_table trace.sampling.scopeTrace
    (List.nodup_iff_pairwise_ne.mpr (represented.1.2.imp (by omega)))] at returned
  split at returned
  · contradiction
  · rename_i checks
    have inputCheck : (normalize ((inputSupport transformer).map (table trace.inputs))).length =
        (inputSupport transformer).length := by
      rw [inputValues, ← inputLength]
      exact Classical.not_not.mp checks
    dsimp only at returned
    split at returned
    · rename_i scopeCheck
      have scopeDistinct := (scope_collision_check transformer
        (table trace.scopes) (table trace.inputs)).mp scopeCheck
      simp only [Return.ok.injEq] at returned
      unfold remapModel
      rw [ite_eq_left ⟨inputCheck, scopeDistinct⟩, returned]
    · contradiction

theorem remapTrace_injective {State inputCall scopeCall transformer result}
    (trace : @RemapTrace State inputCall scopeCall transformer result)
    (represented : Representation transformer) :
    (∀ a ∈ inputSupport transformer, ∀ b ∈ inputSupport transformer,
      table trace.inputs a = table trace.inputs b → a = b) ∧
    (∀ a ∈ keys transformer.scopes, ∀ b ∈ keys transformer.scopes,
      table trace.scopes a = table trace.scopes b → a = b) :=
  remap_success_injective _ _ _ _ (remapTrace_result trace represented)

theorem input_collision_rejected (transformer : Transformer) (inputs scopes : List (Nat × Nat))
    (collision : (normalize (inputs.map Prod.snd)).length ≠ inputs.length) :
    remapReturn transformer inputs scopes = .collisionFailure := by
  simp [remapReturn, collision]

theorem scope_collision_rejected (transformer : Transformer) (inputs scopes : List (Nat × Nat))
    (inputOK : (normalize (inputs.map Prod.snd)).length = inputs.length)
    (collision : adjacentDistinct (keys (sortEntries (sampledEntries transformer.scopes
      (scopes.map Prod.snd) (table inputs)))) = false) :
    remapReturn transformer inputs scopes = .collisionFailure := by
  simp [remapReturn, inputOK, collision]

/-- Inductively successful private calls. Atomic fields are transcribed from
the native constructors. `then` and `remap` require local execution traces,
and contain neither an R166 result equality nor a Generated premise. -/
inductive Successful : Transformer → Prop where
  | identity : Successful ⟨[], []⟩
  | stamp (tag : UInt32) : Successful ⟨[encodeId tag], []⟩
  | protect (scope tag : UInt32) : Successful ⟨[], [(encodeId scope, ⟨true, [encodeId tag]⟩)]⟩
  | release (scope : UInt32) : Successful ⟨[], [(encodeId scope, ⟨false, []⟩)]⟩
  | then {first second result} : Successful first → Successful second →
      ThenTrace first second result → Successful result
  | remap {State : Type} {inputCall scopeCall : State → Nat → State → Nat → Prop}
      {transformer result} : Successful transformer →
      RemapTrace inputCall scopeCall transformer result → Successful result

theorem successful_generated {transformer} (trace : Successful transformer) :
    Generated transformer := by
  induction trace with
  | identity => exact .identity
  | stamp tag => exact .stamp tag
  | protect scope tag => exact .protect scope tag
  | release scope => exact .release scope
  | «then» _ _ operation hf hs =>
      rw [thenTrace_result operation (generated_representation _ hf).1 (generated_representation _ hs).1]
      exact .then hf hs
  | remap _ operation ih =>
      exact .remap (table operation.scopes) (table operation.inputs) ih
        (remapTrace_result operation (generated_representation _ ih))

theorem successful_representation {transformer} (trace : Successful transformer) :
    Representation transformer := generated_representation _ (successful_generated trace)

/-- The API trace keeps native u32 fields at each successful return. Results
are indexed by the locally constructed fields; no final R166 field equality is
an execution premise. Nonprimitive encoded operations overapproximate u32
arithmetic only by admitting more Nat traces, never by asserting such a trace
was executed by Rust. -/
inductive NativeTrace : NativeFields → Prop where
  | identity : NativeTrace ⟨[], []⟩
  | stamp (tag : UInt32) : NativeTrace ⟨[tag], []⟩
  | protect (scope tag : UInt32) : NativeTrace ⟨[], [⟨scope, true, [tag]⟩]⟩
  | release (scope : UInt32) : NativeTrace ⟨[], [⟨scope, false, []⟩]⟩
  | then {first second result : NativeFields} : NativeTrace first → NativeTrace second →
      ThenTrace (encodeFields first) (encodeFields second) (encodeFields result) → NativeTrace result
  | remap {State : Type} {inputCall scopeCall : State → Nat → State → Nat → Prop}
      {transformer result : NativeFields} : NativeTrace transformer →
      RemapTrace inputCall scopeCall (encodeFields transformer) (encodeFields result) → NativeTrace result

theorem nativeTrace_successful {native : NativeFields} (trace : NativeTrace native) :
    Successful (encodeFields native) := by
  induction trace with
  | identity => exact .identity
  | stamp tag => exact .stamp tag
  | protect scope tag => exact .protect scope tag
  | release scope => exact .release scope
  | «then» _ _ operation hf hs => exact .then hf hs operation
  | remap _ operation ih => exact .remap ih operation

theorem nativeTrace_generated {native : NativeFields} (trace : NativeTrace native) :
    Generated (encodeFields native) := successful_generated (nativeTrace_successful trace)

theorem successful_evaluate_equivalent (native : NativeFields) (initial : State)
    (trace : Successful (encodeFields native)) :
    Equivalent (evaluateCursor (encodeFields native) initial)
      ((encodeFields native).evaluate initial) :=
  generated_evaluate_equivalent _ initial (successful_generated trace)

/-- R166/R165 applied only after the successful source trace derived Generated.
The initial state remains arbitrary, including unsorted and duplicate lists. -/
theorem nativeTrace_evaluate_equivalent (native : NativeFields) (initial : State)
    (trace : NativeTrace native) :
    Equivalent (evaluateCursor (encodeFields native) initial)
      ((encodeFields native).evaluate initial) :=
  generated_evaluate_equivalent _ initial (nativeTrace_generated trace)

theorem thenTrace_denotation {first second result} (trace : ThenTrace first second result)
    (firstOrdered : Canonical first) (secondOrdered : Canonical second) (initial : State) :
    Equivalent (result.evaluate initial) (second.evaluate (first.evaluate initial)) := by
  rw [thenTrace_result trace firstOrdered secondOrdered]
  exact thenModel_denotation first second initial

end YulangClosure.NativeScopeExecutionR167
