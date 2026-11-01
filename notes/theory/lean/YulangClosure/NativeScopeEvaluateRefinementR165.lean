import YulangClosure.NativeScopeTransformer

/-!
Successful, allocation-free content of `candidate_scope.rs::ScopeTransformer::evaluate`.
The lists below are the two unconsumed cursor suffixes; every recursive call
advances exactly the cursor(s) advanced by the Rust loop. `Canonical` is the
ordered stamped-input/scope-key part of the representation invariant required
by this model. The inspected private Rust constructors, `then`, and successful
`remap` preserve it; this module does not formalize the Rust-to-Lean encoding or
prove binary-search correspondence.
-/
namespace YulangClosure.NativeScopeEvaluateRefinementR165

open NativeScopeTransformer

def normalize (xs : List Nat) : List Nat :=
  (xs.eraseDups).mergeSort (fun a b => decide (a ≤ b))

theorem mem_normalize (xs : List Nat) (x : Nat) :
    x ∈ normalize xs ↔ x ∈ xs := by
  simp [normalize]

theorem nodup_eraseDups_nat (xs : List Nat) : xs.eraseDups.Nodup := by
  have aux : ∀ n (ys : List Nat), ys.length = n → ys.eraseDups.Nodup := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ys hlen
      cases ys with
      | nil => simp
      | cons x rest =>
        rw [List.eraseDups_cons]
        simp only [List.nodup_cons]
        constructor
        · simp
        · apply ih (List.length (rest.filter fun b => !b == x))
          · have hle := List.length_filter_le (fun b => !b == x) rest
            simp only [List.length_cons] at hlen
            omega
          · rfl
  exact aux xs.length xs rfl

theorem sorted_normalize (xs : List Nat) :
    (normalize xs).Pairwise (· < ·) := by
  have hle : (normalize xs).Pairwise (fun a b => decide (a ≤ b)) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact Nat.le_trans hab hbc)
      (fun a b => by simp; omega) _
  have hn : (normalize xs).Nodup :=
    (List.mergeSort_perm xs.eraseDups (fun a b => decide (a ≤ b))).symm.nodup
      (nodup_eraseDups_nat xs)
  exact List.Pairwise.imp₂ (fun a b hab hne => by
      have hab' : a ≤ b := by simpa only [decide_eq_true_eq] using hab
      exact Nat.lt_of_le_of_ne hab' hne)
    hle (List.nodup_iff_pairwise_ne.mp hn)

def unionCursor : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x < y then x :: unionCursor xs (y :: ys)
      else if y < x then y :: unionCursor (x :: xs) ys
      else x :: unionCursor xs ys
termination_by xs ys => xs.length + ys.length

def active (entry : Entry) (inputs : List Nat) (inherited : Bool) : Bool :=
  (entry.keep && inherited) || decide (Missing entry.missing inputs)

def protectionCursor (inputs : List Nat) :
    List Nat → List (Nat × Entry) → List Nat
  | [], [] => []
  | xs, [] => xs
  | [], (scope, entry) :: es =>
      (if active entry inputs false then [scope] else []) ++ protectionCursor inputs [] es
  | x :: xs, (scope, entry) :: es =>
      if x < scope then x :: protectionCursor inputs xs ((scope, entry) :: es)
      else if scope < x then
        (if active entry inputs false then [scope] else []) ++
          protectionCursor inputs (x :: xs) es
      else
        (if active entry inputs true then [scope] else []) ++
          protectionCursor inputs xs es
termination_by xs es => xs.length + es.length

def evaluateCursor (transformer : Transformer) (initial : State) : State :=
  let inputs := normalize initial.inputs
  let protections := normalize initial.protections
  ⟨unionCursor inputs transformer.stamped,
    protectionCursor inputs protections transformer.scopes⟩

/-- A state of the Rust protection loop: emitted prefix and two remaining
cursor suffixes. The entry suffix carries the still unvisited scope records. -/
structure ProtectionCursor where
  emitted : List Nat
  inherited : List Nat
  entries : List (Nat × Entry)

def ProtectionCursor.step (inputs : List Nat) (cursor : ProtectionCursor) :
    Option ProtectionCursor :=
  match cursor.inherited, cursor.entries with
  | [], [] => none
  | x :: xs, [] => some ⟨cursor.emitted ++ [x], xs, []⟩
  | [], (scope, entry) :: es =>
      some ⟨cursor.emitted ++ (if active entry inputs false then [scope] else []), [], es⟩
  | x :: xs, (scope, entry) :: es =>
      if x < scope then
        some ⟨cursor.emitted ++ [x], xs, (scope, entry) :: es⟩
      else if scope < x then
        some ⟨cursor.emitted ++ (if active entry inputs false then [scope] else []),
          x :: xs, es⟩
      else
        some ⟨cursor.emitted ++ (if active entry inputs true then [scope] else []), xs, es⟩

/-- Concrete emitted-prefix/remaining-suffix invariant for one Rust cursor
transition, before any denotational simplification. -/
theorem ProtectionCursor.step_preserves_remainder (inputs : List Nat)
    (cursor next : ProtectionCursor)
    (step : cursor.step inputs = some next) :
    cursor.emitted ++ protectionCursor inputs cursor.inherited cursor.entries =
      next.emitted ++ protectionCursor inputs next.inherited next.entries := by
  cases cursor with
  | mk emitted inherited entries =>
    cases inherited with
    | nil =>
      cases entries with
      | nil => simp [ProtectionCursor.step] at step
      | cons head rest =>
        rcases head with ⟨scope, entry⟩
        simp only [ProtectionCursor.step, Option.some.injEq] at step
        subst next
        simp [protectionCursor, List.append_assoc]
    | cons x xs =>
      cases entries with
      | nil =>
        simp only [ProtectionCursor.step, Option.some.injEq] at step
        subst next
        have hnil : protectionCursor inputs xs [] = xs := by cases xs <;> simp [protectionCursor]
        simp [protectionCursor, hnil, List.append_assoc]
      | cons head rest =>
        rcases head with ⟨scope, entry⟩
        by_cases hxs : x < scope
        · simp only [ProtectionCursor.step, if_pos hxs, Option.some.injEq] at step
          subst next
          simp [protectionCursor, hxs, List.append_assoc]
        · by_cases hsx : scope < x
          · simp only [ProtectionCursor.step, if_neg hxs, if_pos hsx,
              Option.some.injEq] at step
            subst next
            simp [protectionCursor, hxs, hsx, List.append_assoc]
          · simp only [ProtectionCursor.step, if_neg hxs, if_neg hsx,
              Option.some.injEq] at step
            subst next
            simp [protectionCursor, hxs, hsx, List.append_assoc]

inductive ProtectionCursor.Steps (inputs : List Nat) :
    ProtectionCursor → ProtectionCursor → Prop where
  | refl (cursor : ProtectionCursor) : Steps inputs cursor cursor
  | advance {start middle finish : ProtectionCursor}
      (step : start.step inputs = some middle)
      (later : Steps inputs middle finish) : Steps inputs start finish

theorem ProtectionCursor.Steps_preserves_remainder (inputs : List Nat)
    {start finish : ProtectionCursor} (steps : Steps inputs start finish) :
    start.emitted ++ protectionCursor inputs start.inherited start.entries =
      finish.emitted ++ protectionCursor inputs finish.inherited finish.entries := by
  induction steps with
  | refl => rfl
  | advance step later ih =>
      exact (ProtectionCursor.step_preserves_remainder inputs _ _ step).trans ih

/-- The cursor suffixes contain precisely the elements not yet appended. -/
theorem unionCursor_mem (xs ys : List Nat) (x : Nat) :
    x ∈ unionCursor xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  have aux : ∀ n (xs ys : List Nat), xs.length + ys.length = n →
      ∀ x, x ∈ unionCursor xs ys ↔ x ∈ xs ∨ x ∈ ys := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro xs ys hlen x
      cases xs with
      | nil => simp [unionCursor]
      | cons a as =>
        cases ys with
        | nil => simp [unionCursor]
        | cons b bs =>
          by_cases hab : a < b
          · simp only [unionCursor, if_pos hab, List.mem_cons]
            rw [ih (as.length + (b :: bs).length) (by
              simp only [List.length_cons] at hlen ⊢
              omega)
              as (b :: bs) rfl x]
            simp only [List.mem_cons]
            simp only [or_assoc, or_left_comm, or_comm]
          · by_cases hba : b < a
            · simp only [unionCursor, if_neg hab, if_pos hba, List.mem_cons]
              rw [ih ((a :: as).length + bs.length) (by
                simp only [List.length_cons] at hlen ⊢
                omega)
                (a :: as) bs rfl x]
              simp [List.mem_cons, or_assoc, or_left_comm, or_comm]
            · simp only [unionCursor, if_neg hab, if_neg hba, List.mem_cons]
              have heq : a = b := by omega
              subst b
              rw [ih (as.length + bs.length) (by
                simp only [List.length_cons] at hlen ⊢
                omega)
                as bs rfl x]
              simp [List.mem_cons, or_assoc, or_left_comm, or_comm]
  exact aux (xs.length + ys.length) xs ys rfl x

theorem active_false (entry : Entry) (inputs : List Nat) :
    active entry inputs false = true ↔ Missing entry.missing inputs := by
  simp [active]

theorem active_true (entry : Entry) (inputs : List Nat) :
    active entry inputs true = true ↔
      entry.keep = true ∨ Missing entry.missing inputs := by
  simp [active, Bool.or_eq_true, Bool.and_eq_true]

def Canonical (transformer : Transformer) : Prop :=
  transformer.stamped.Pairwise (· < ·) ∧
    (keys transformer.scopes).Pairwise (· < ·)

private theorem head_lt_tail {a : Nat} {xs : List Nat}
    (hs : (a :: xs).Pairwise (· < ·)) {x : Nat} (hx : x ∈ xs) : a < x :=
  (List.pairwise_cons.mp hs).1 x hx

private theorem head_not_tail {a : Nat} {xs : List Nat}
    (hs : (a :: xs).Pairwise (· < ·)) : a ∉ xs := by
  intro ha
  have := head_lt_tail hs ha
  omega

theorem protectionCursor_mem (inputs left : List Nat) (entries : List (Nat × Entry))
    (hleft : left.Pairwise (· < ·))
    (hentries : (keys entries).Pairwise (· < ·)) (x : Nat) :
    x ∈ protectionCursor inputs left entries ↔
      ((entryAt entries x).keep = true ∧ x ∈ left) ∨
        Missing (entryAt entries x).missing inputs := by
  have aux : ∀ n (left : List Nat) (entries : List (Nat × Entry)),
      left.length + entries.length = n →
      left.Pairwise (· < ·) → (keys entries).Pairwise (· < ·) →
      ∀ x, x ∈ protectionCursor inputs left entries ↔
        ((entryAt entries x).keep = true ∧ x ∈ left) ∨
          Missing (entryAt entries x).missing inputs := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro left entries hlen hl he x
      cases left with
      | nil =>
        cases entries with
        | nil => simp [protectionCursor, entryAt, Missing, identityEntry]
        | cons head rest =>
          rcases head with ⟨scope, entry⟩
          by_cases same : x = scope
          · subst x
            have hne : scope ∉ keys rest := head_not_tail he
            have htail := ih rest.length (by simp at hlen; omega) [] rest (by simp)
              (by simp) (List.pairwise_cons.mp he).2 scope
            have htailnot : scope ∉ protectionCursor inputs [] rest := by
              rw [htail]
              simp [entryAt_absent rest scope hne, identityEntry, Missing]
            simp [protectionCursor, active_false, entryAt, htailnot]
          · have htail := ih rest.length (by simp at hlen; omega) [] rest (by simp)
              (by simp) (List.pairwise_cons.mp he).2 x
            simp [protectionCursor, active_false, entryAt, same, Ne.symm same, htail]
      | cons a as =>
        cases entries with
        | nil => simp [protectionCursor, entryAt, Missing, identityEntry]
        | cons head rest =>
          rcases head with ⟨scope, entry⟩
          by_cases has : a < scope
          · have htail := ih (as.length + ((scope, entry) :: rest).length)
                (by simp only [List.length_cons] at hlen ⊢; omega)
                as ((scope, entry) :: rest) rfl (List.pairwise_cons.mp hl).2 he x
            by_cases same : x = a
            · subst x
              have hne : a ∉ keys ((scope, entry) :: rest) := by
                simp only [keys, List.map_cons, List.mem_cons, not_or]
                constructor
                · omega
                · intro found
                  have hlt := head_lt_tail he found
                  omega
              have htailnot : a ∉ protectionCursor inputs as ((scope, entry) :: rest) := by
                rw [htail]
                simp [entryAt_absent _ a hne, head_not_tail hl, identityEntry, Missing]
              simp [protectionCursor, has, htailnot,
                entryAt_absent _ a hne, identityEntry, Missing]
            · simp [protectionCursor, has, same, htail]
          · by_cases hsa : scope < a
            · have htail := ih ((a :: as).length + rest.length)
                  (by simp only [List.length_cons] at hlen ⊢; omega)
                  (a :: as) rest rfl hl (List.pairwise_cons.mp he).2 x
              by_cases same : x = scope
              · subst x
                have hnot : scope ∉ a :: as := by
                  simp only [List.mem_cons, not_or]
                  constructor
                  · omega
                  · intro found
                    have hlt := head_lt_tail hl found
                    omega
                have hne : scope ∉ keys rest := head_not_tail he
                have htailnot : scope ∉ protectionCursor inputs (a :: as) rest := by
                  rw [htail]
                  simp [entryAt_absent rest scope hne, hnot, identityEntry, Missing]
                simp [protectionCursor, has, hsa, htailnot, entryAt, hnot,
                  active_false]
              · simp [protectionCursor, has, hsa, same, Ne.symm same, entryAt, htail]
            · have same : a = scope := by omega
              subst scope
              have htail := ih (as.length + rest.length)
                (by simp only [List.length_cons] at hlen ⊢; omega)
                as rest rfl (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp he).2 x
              by_cases same : x = a
              · subst x
                have hnot : a ∉ as := head_not_tail hl
                have hne : a ∉ keys rest := head_not_tail he
                have htailnot : a ∉ protectionCursor inputs as rest := by
                  rw [htail]
                  simp [entryAt_absent rest a hne, hnot, identityEntry, Missing]
                simp [protectionCursor, has, htailnot, entryAt, hnot, active_true]
              · simp [protectionCursor, has, same, Ne.symm same, entryAt, htail]
  exact aux (left.length + entries.length) left entries rfl hleft hentries x

private theorem missing_entry_support (entries : List (Nat × Entry)) (inputs : List Nat)
    (scope : Nat) (missing : Missing (entryAt entries scope).missing inputs) :
    scope ∈ keys entries := by
  by_cases present : scope ∈ keys entries
  · exact present
  · have neutral := entryAt_absent entries scope present
    simp [neutral, identityEntry, Missing] at missing

theorem protectionCursor_support (inputs left : List Nat) (entries : List (Nat × Entry))
    (hleft : left.Pairwise (· < ·))
    (hentries : (keys entries).Pairwise (· < ·)) (scope : Nat)
    (present : scope ∈ protectionCursor inputs left entries) :
    scope ∈ left ∨ scope ∈ keys entries := by
  have h := (protectionCursor_mem inputs left entries hleft hentries scope).mp present
  rcases h with ⟨_, inherited⟩ | missing
  · exact Or.inl inherited
  · exact Or.inr (missing_entry_support entries inputs scope missing)

theorem unionCursor_sorted (xs ys : List Nat)
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·)) :
    (unionCursor xs ys).Pairwise (· < ·) := by
  have aux : ∀ n (xs ys : List Nat), xs.length + ys.length = n →
      xs.Pairwise (· < ·) → ys.Pairwise (· < ·) →
      (unionCursor xs ys).Pairwise (· < ·) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro xs ys hlen hs ht
      cases xs with
      | nil => simpa [unionCursor] using ht
      | cons a as =>
        cases ys with
        | nil => simpa [unionCursor] using hs
        | cons b bs =>
          by_cases hab : a < b
          · simp only [unionCursor, if_pos hab, List.pairwise_cons]
            constructor
            · intro z hz
              rcases (unionCursor_mem as (b :: bs) z).mp hz with ha | hb
              · exact head_lt_tail hs ha
              · rcases List.mem_cons.mp hb with rfl | hb'
                · exact hab
                · exact Nat.lt_trans hab (head_lt_tail ht hb')
            · exact ih (as.length + (b :: bs).length)
                (by simp only [List.length_cons] at hlen ⊢; omega)
                as (b :: bs) rfl (List.pairwise_cons.mp hs).2 ht
          · by_cases hba : b < a
            · simp only [unionCursor, if_neg hab, if_pos hba, List.pairwise_cons]
              constructor
              · intro z hz
                rcases (unionCursor_mem (a :: as) bs z).mp hz with ha | hb
                · rcases List.mem_cons.mp ha with rfl | ha'
                  · exact hba
                  · exact Nat.lt_trans hba (head_lt_tail hs ha')
                · exact head_lt_tail ht hb
              · exact ih ((a :: as).length + bs.length)
                  (by simp only [List.length_cons] at hlen ⊢; omega)
                  (a :: as) bs rfl hs (List.pairwise_cons.mp ht).2
            · have same : a = b := by omega
              subst b
              simp only [unionCursor, if_neg hab, if_neg hba, List.pairwise_cons]
              constructor
              · intro z hz
                rcases (unionCursor_mem as bs z).mp hz with ha | hb
                · exact head_lt_tail hs ha
                · exact head_lt_tail ht hb
              · exact ih (as.length + bs.length)
                  (by simp only [List.length_cons] at hlen ⊢; omega)
                  as bs rfl (List.pairwise_cons.mp hs).2 (List.pairwise_cons.mp ht).2
  exact aux (xs.length + ys.length) xs ys rfl hx hy

theorem protectionCursor_sorted (inputs left : List Nat) (entries : List (Nat × Entry))
    (hleft : left.Pairwise (· < ·))
    (hentries : (keys entries).Pairwise (· < ·)) :
    (protectionCursor inputs left entries).Pairwise (· < ·) := by
  have aux : ∀ n (left : List Nat) (entries : List (Nat × Entry)),
      left.length + entries.length = n →
      left.Pairwise (· < ·) → (keys entries).Pairwise (· < ·) →
      (protectionCursor inputs left entries).Pairwise (· < ·) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro left entries hlen hl he
      cases left with
      | nil =>
        cases entries with
        | nil => simp [protectionCursor]
        | cons head rest =>
          rcases head with ⟨scope, entry⟩
          have htail := ih rest.length (by simp at hlen; omega) [] rest (by simp)
            (by simp)
            (List.pairwise_cons.mp he).2
          by_cases activeNow : active entry inputs false = true
          · simp only [protectionCursor, activeNow, ite_true, List.nil_append,
              List.singleton_append, List.pairwise_cons]
            constructor
            · intro z hz
              rcases protectionCursor_support inputs [] rest (by simp)
                  (List.pairwise_cons.mp he).2 z hz with impossible | supported
              · simp at impossible
              · exact head_lt_tail he supported
            · exact htail
          · simpa [protectionCursor, activeNow] using htail
      | cons a as =>
        cases entries with
        | nil => simpa [protectionCursor] using hl
        | cons head rest =>
          rcases head with ⟨scope, entry⟩
          by_cases has : a < scope
          · have htail := ih (as.length + ((scope, entry) :: rest).length)
                (by simp only [List.length_cons] at hlen ⊢; omega)
                as ((scope, entry) :: rest) rfl (List.pairwise_cons.mp hl).2 he
            simp only [protectionCursor, if_pos has, List.pairwise_cons]
            constructor
            · intro z hz
              rcases protectionCursor_support inputs as ((scope, entry) :: rest)
                  (List.pairwise_cons.mp hl).2 he z hz with inherited | supported
              · exact head_lt_tail hl inherited
              · rcases List.mem_cons.mp supported with equal | inRest
                · have : z = scope := by simpa [keys] using equal
                  omega
                · have hlt : scope < z := head_lt_tail he (by simpa [keys] using inRest)
                  omega
            · exact htail
          · by_cases hsa : scope < a
            · have htail := ih ((a :: as).length + rest.length)
                  (by simp only [List.length_cons] at hlen ⊢; omega)
                  (a :: as) rest rfl hl (List.pairwise_cons.mp he).2
              by_cases activeNow : active entry inputs false = true
              · simp only [protectionCursor, if_neg has, if_pos hsa,
                  activeNow, ite_true, List.singleton_append, List.pairwise_cons]
                constructor
                · intro z hz
                  rcases protectionCursor_support inputs (a :: as) rest hl
                      (List.pairwise_cons.mp he).2 z hz with inherited | supported
                  · rcases List.mem_cons.mp inherited with equal | inRest
                    · have : z = a := equal
                      omega
                    · have hlt := head_lt_tail hl inRest
                      omega
                  · exact head_lt_tail he supported
                · exact htail
              · simpa [protectionCursor, has, hsa, activeNow] using htail
            · have same : a = scope := by omega
              subst scope
              have htail := ih (as.length + rest.length)
                (by simp only [List.length_cons] at hlen ⊢; omega)
                as rest rfl (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp he).2
              by_cases activeNow : active entry inputs true = true
              · simp only [protectionCursor, if_neg has, if_neg hsa,
                  activeNow, ite_true, List.singleton_append, List.pairwise_cons]
                constructor
                · intro z hz
                  rcases protectionCursor_support inputs as rest
                      (List.pairwise_cons.mp hl).2 (List.pairwise_cons.mp he).2 z hz with
                      inherited | supported
                  · exact head_lt_tail hl inherited
                  · exact head_lt_tail he supported
                · exact htail
              · simpa [protectionCursor, has, activeNow] using htail
  exact aux (left.length + entries.length) left entries rfl hleft hentries

def CanonicalState (state : State) : Prop :=
  state.inputs.Pairwise (· < ·) ∧ state.protections.Pairwise (· < ·)

theorem evaluateCursor_canonical (transformer : Transformer) (initial : State)
    (canonical : Canonical transformer) :
    CanonicalState (evaluateCursor transformer initial) := by
  constructor
  · exact unionCursor_sorted _ _ (sorted_normalize initial.inputs) canonical.1
  · exact protectionCursor_sorted _ _ _ (sorted_normalize initial.protections) canonical.2

theorem evaluateCursor_nodup (transformer : Transformer) (initial : State)
    (canonical : Canonical transformer) :
    (evaluateCursor transformer initial).inputs.Nodup ∧
      (evaluateCursor transformer initial).protections.Nodup := by
  obtain ⟨hi, hp⟩ := evaluateCursor_canonical transformer initial canonical
  constructor
  · exact List.nodup_iff_pairwise_ne.mpr (hi.imp (by omega))
  · exact List.nodup_iff_pairwise_ne.mpr (hp.imp (by omega))

theorem evaluateCursor_equivalent (transformer : Transformer) (initial : State)
    (canonical : Canonical transformer) :
    Equivalent (evaluateCursor transformer initial) (transformer.evaluate initial) := by
  let normalized : State := ⟨normalize initial.inputs, normalize initial.protections⟩
  have normalized_equiv : Equivalent normalized initial := by
    constructor
    · intro tag
      exact mem_normalize initial.inputs tag
    · intro scope
      exact mem_normalize initial.protections scope
  have cursor_equiv : Equivalent (evaluateCursor transformer initial)
      (transformer.evaluate normalized) := by
    constructor
    · intro tag
      simp only [evaluateCursor, Transformer.evaluate, List.mem_append]
      exact unionCursor_mem _ _ tag
    · intro scope
      rw [NativeScopeTransformer.evaluate_protection]
      exact protectionCursor_mem (normalize initial.inputs)
        (normalize initial.protections) transformer.scopes
        (sorted_normalize initial.protections) canonical.2 scope
  exact cursor_equiv.trans (NativeScopeTransformer.evaluate_congr transformer normalized_equiv)

end YulangClosure.NativeScopeEvaluateRefinementR165
