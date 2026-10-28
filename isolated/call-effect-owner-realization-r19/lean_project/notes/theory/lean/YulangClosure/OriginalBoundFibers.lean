import YulangClosure.NativeRelationInterner

/-!
The actual append-only bound-fiber vector and its stored linked heads.
Keys are parametric so the full native BoundKey, including both endpoint
kinds and polarity, can be retained without an endpoint quotient.
Raw relation IDs are never replaced by semantic equivalence classes.
This module does not supply dependency/evidence publication or source typing.
-/
namespace YulangClosure.OriginalBoundFibers

open NativeRelationInterner (Map empty put)

variable {B : Type}

structure Entry (B : Type) where
  key : B
  relation : Nat
  previous : Option Nat
  deriving DecidableEq, Repr

structure Store (B : Type) where
  entries : List (Entry B) := []
  heads : Map B := empty

def Backward (entries : List (Entry B)) : Prop :=
  ∀ (index : Nat) (entry : Entry B), entries[index]? = some entry →
    ∀ previous, entry.previous = some previous → previous < index

def cursorRank : Option Nat → Nat
  | none => 0
  | some index => index + 1

/-- A read-only interpreter of the real linked cursor. Its recursion is
justified by the original older-index invariant, not a supplied fuel cap.
The absent-index branch is unreachable from a formed stored head. -/
def walk (entries : List (Entry B)) (backward : Backward entries)
    (cursor : Option Nat) : List (Nat × Entry B) :=
  match cursor with
  | none => []
  | some index =>
    match _found : entries[index]? with
    | none => []
    | some entry => (index, entry) :: walk entries backward entry.previous
termination_by cursorRank cursor
decreasing_by
  cases previous : entry.previous with
  | none => simp [cursorRank]
  | some old =>
    have earlier := backward index entry _found old previous
    simp only [cursorRank]
    omega

structure Valid (s : Store B) : Prop where
  backward : Backward s.entries
  heads : ∀ (key : B) (index : Nat), s.heads key = some index →
    ∃ entry : Entry B, s.entries[index]? = some entry ∧ entry.key = key
  links : ∀ (index : Nat) (entry : Entry B) (previous : Nat), s.entries[index]? = some entry →
    entry.previous = some previous →
    ∃ old : Entry B, s.entries[previous]? = some old ∧ old.key = entry.key

def fibers (s : Store B) (valid : Valid s) (key : B) : List Nat :=
  (walk s.entries valid.backward (s.heads key)).map (fun item => item.2.relation)

theorem valid_empty : Valid ({} : Store B) := by
  constructor
  · intro index entry found
    simp at found
  · intro key index found
    cases found
  · intro index entry previous found
    simp at found

/-- The successful publication part of Context.attach after both reserves.
The stored predecessor is the old head of this complete BoundKey. -/
def append [DecidableEq B] (s : Store B) (key : B) (relation : Nat) : Store B :=
  { entries := s.entries ++ [⟨key, relation, s.heads key⟩]
    heads := put s.heads key s.entries.length }

theorem append_old [DecidableEq B] (s : Store B) (key : B) (relation : Nat)
    {index : Nat} {entry : Entry B} (found : s.entries[index]? = some entry) :
    (append s key relation).entries[index]? = some entry := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  simpa [append, List.getElem?_append_left bound] using found

theorem append_new [DecidableEq B] (s : Store B) (key : B) (relation : Nat) :
    (append s key relation).entries[s.entries.length]? =
      some ⟨key, relation, s.heads key⟩ ∧
    (append s key relation).heads key = some s.entries.length := by
  simp [append, put]

theorem append_valid [DecidableEq B] {s : Store B} (valid : Valid s)
    (key : B) (relation : Nat) : Valid (append s key relation) := by
  have splitEntry : ∀ index entry,
      (append s key relation).entries[index]? = some entry →
      s.entries[index]? = some entry ∨
        (index = s.entries.length ∧ entry = ⟨key, relation, s.heads key⟩) := by
    intro index entry found
    by_cases old : index < s.entries.length
    · exact Or.inl (by simpa [append, List.getElem?_append_left old] using found)
    · have bound := (List.getElem?_eq_some_iff.mp found).1
      have same : index = s.entries.length := by
        simp only [append, List.length_append, List.length_singleton] at bound
        omega
      subst index
      exact Or.inr ⟨rfl, by simpa [append] using found.symm⟩
  constructor
  · intro index entry found previous link
    rcases splitEntry index entry found with old | ⟨rfl, rfl⟩
    · exact valid.backward index entry old previous link
    · obtain ⟨prior, stored, _⟩ := valid.heads key previous link
      exact (List.getElem?_eq_some_iff.mp stored).1
  · intro query index found
    by_cases same : query = key
    · subst query
      have indexIs : s.entries.length = index := by simpa [append, put] using found
      subst index
      exact ⟨_, (append_new s key relation).1, rfl⟩
    · have old : s.heads query = some index := by simpa [append, put, same] using found
      obtain ⟨entry, stored, named⟩ := valid.heads query index old
      exact ⟨entry, append_old s key relation stored, named⟩
  · intro index entry previous found link
    rcases splitEntry index entry found with old | ⟨rfl, rfl⟩
    · obtain ⟨prior, stored, named⟩ := valid.links index entry previous old link
      exact ⟨prior, append_old s key relation stored, named⟩
    · obtain ⟨prior, stored, named⟩ := valid.heads key previous link
      exact ⟨prior, append_old s key relation stored, named⟩

theorem walk_none (entries : List (Entry B)) (backward : Backward entries) :
    walk entries backward none = [] := by rw [walk]

theorem walk_some (entries : List (Entry B)) (backward : Backward entries)
    {index : Nat} {entry : Entry B} (found : entries[index]? = some entry) :
    walk entries backward (some index) =
      (index, entry) :: walk entries backward entry.previous := by
  rw [walk]
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i other same
    have equal : other = entry := Option.some.inj (same.symm.trans found)
    subst other
    rfl

theorem walk_extends {before after : List (Entry B)}
    (first : Backward before) (last : Backward after)
    (extension : NativeValuePorts.Extends before after) (cursor : Option Nat)
    (bounded : ∀ index, cursor = some index → index < before.length) :
    walk after last cursor = walk before first cursor := by
  cases cursor with
  | none => rw [walk_none, walk_none]
  | some index =>
    have bound := bounded index rfl
    let entry := before[index]'bound
    have found : before[index]? = some entry := List.getElem?_eq_getElem bound
    rw [walk_some after last (extension index entry found), walk_some before first found]
    congr 1
    apply walk_extends first last extension entry.previous
    intro previous link
    exact Nat.lt_trans (first index entry found previous link) bound
termination_by cursorRank cursor
decreasing_by
  subst cursor
  cases previous : entry.previous with
  | none => simp [cursorRank]
  | some old =>
    have earlier := first index entry found old previous
    simp only [cursorRank]
    omega

theorem head_bounded {s : Store B} (valid : Valid s) (key : B) :
    ∀ index, s.heads key = some index → index < s.entries.length := by
  intro index found
  obtain ⟨entry, stored, _⟩ := valid.heads key index found
  exact (List.getElem?_eq_some_iff.mp stored).1

/-- Appending changes the live head but cannot change an already captured
cursor's complete readback. This includes attachment back to the source key. -/
theorem append_captured_cursor [DecidableEq B] {s : Store B} (valid : Valid s)
    (key : B) (relation : Nat) (cursor : Option Nat)
    (bounded : ∀ index, cursor = some index → index < s.entries.length) :
    walk (append s key relation).entries (append_valid valid key relation).backward cursor =
      walk s.entries valid.backward cursor :=
  walk_extends valid.backward (append_valid valid key relation).backward
    (fun _ _ found => append_old s key relation found) cursor bounded

theorem append_fibers [DecidableEq B] {s : Store B} (valid : Valid s)
    (key : B) (relation : Nat) :
    fibers (append s key relation) (append_valid valid key relation) key =
      relation :: fibers s valid key := by
  unfold fibers
  rw [(append_new s key relation).2, walk_some _ _ (append_new s key relation).1]
  simp only [List.map_cons]
  rw [append_captured_cursor valid key relation (s.heads key) (head_bounded valid key)]

theorem append_other_fibers [DecidableEq B] {s : Store B} (valid : Valid s)
    (key other : B) (relation : Nat) (different : other ≠ key) :
    fibers (append s key relation) (append_valid valid key relation) other =
      fibers s valid other := by
  have heads : (append s key relation).heads other = s.heads other := by
    simp [append, put, different]
  unfold fibers
  rw [heads, append_captured_cursor valid key relation (s.heads other) (head_bounded valid other)]

structure Resources where
  heads : Bool := true
  entries : Bool := true
  deriving DecidableEq, Repr

inductive Outcome where
  | complete | exhausted
  deriving DecidableEq, Repr

/-- Exact Context.attach decision order on the represented fields: scan the
actual chain for the same raw RelationId; reserve the head map then vector;
only then update both. Reservation capacity effects are projected out. -/
def attach [DecidableEq B] (s : Store B) (valid : Valid s)
    (resources : Resources) (key : B) (relation : Nat) : Store B × Outcome :=
  if relation ∈ fibers s valid key then (s, .complete)
  else if resources.heads = false then (s, .exhausted)
  else if resources.entries = false then (s, .exhausted)
  else (append s key relation, .complete)

theorem attach_valid [DecidableEq B] (s : Store B) (valid : Valid s)
    (resources : Resources) (key : B) (relation : Nat) :
    Valid (attach s valid resources key relation).1 := by
  unfold attach
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · exact append_valid valid key relation

theorem attach_old [DecidableEq B] (s : Store B) (valid : Valid s)
    (resources : Resources) (key : B) (relation : Nat) :
    NativeValuePorts.Extends s.entries (attach s valid resources key relation).1.entries := by
  intro index entry found
  unfold attach
  split
  · exact found
  · split
    · exact found
    · split
      · exact found
      · exact append_old s key relation found

/-- Successful duplicate attachment retains its exact existing identity;
successful fresh attachment prepends exactly one relation to the linked view.
No semantic equivalence, endpoint-only key or default fiber is substituted. -/
theorem attach_fibers [DecidableEq B] (s : Store B) (valid : Valid s)
    (resources : Resources) (key : B) (relation : Nat)
    (normal : (attach s valid resources key relation).2 = .complete) :
    fibers (attach s valid resources key relation).1
      (attach_valid s valid resources key relation) key =
      if relation ∈ fibers s valid key then fibers s valid key
      else relation :: fibers s valid key := by
  by_cases seen : relation ∈ fibers s valid key
  · simp only [attach, ite_eq_left seen]
  · by_cases heads : resources.heads = false
    · simp [attach, seen, heads] at normal
    · by_cases entries : resources.entries = false
      · simp [attach, seen, heads, entries] at normal
      · simpa only [attach, ite_eq_right seen, ite_eq_right heads, ite_eq_right entries] using
          append_fibers valid key relation

theorem attach_supplies_relation [DecidableEq B] (s : Store B) (valid : Valid s)
    (resources : Resources) (key : B) (relation : Nat)
    (normal : (attach s valid resources key relation).2 = .complete) :
    relation ∈ fibers (attach s valid resources key relation).1
      (attach_valid s valid resources key relation) key := by
  rw [attach_fibers s valid resources key relation normal]
  split
  · assumption
  · exact List.mem_cons_self

theorem attach_captured_cursor [DecidableEq B] (s : Store B) (valid : Valid s)
    (resources : Resources) (key : B) (relation : Nat) (cursor : Option Nat)
    (bounded : ∀ index, cursor = some index → index < s.entries.length) :
    walk (attach s valid resources key relation).1.entries
      (attach_valid s valid resources key relation).backward cursor =
      walk s.entries valid.backward cursor :=
  walk_extends valid.backward (attach_valid s valid resources key relation).backward
    (attach_old s valid resources key relation) cursor bounded

theorem attach_fiber_prefix [DecidableEq B] (s : Store B) (valid : Valid s)
    (resources : Resources) (key : B) (relation : Nat) (query : B) :
    ∃ added, fibers (attach s valid resources key relation).1
      (attach_valid s valid resources key relation) query = added ++ fibers s valid query := by
  unfold attach
  split
  · exact ⟨[], rfl⟩
  · split
    · exact ⟨[], rfl⟩
    · split
      · exact ⟨[], rfl⟩
      · by_cases same : query = key
        · subst query
          exact ⟨[relation], append_fibers valid key relation⟩
        · exact ⟨[], append_other_fibers valid key query relation same⟩

/-- A finite actual sequence of attach calls, including exact reuse and
reservation failure. It supplies no completed subtyping or Replay result. -/
inductive Run [DecidableEq B] : Store B → Store B → Prop
  | nil (s) : Run s s
  | call {first middle} (past : Run first middle) (valid : Valid middle)
      (resources : Resources) (key : B) (relation : Nat) :
      Run first (attach middle valid resources key relation).1

theorem run_valid [DecidableEq B] {first last : Store B}
    (run : Run first last) (valid : Valid first) : Valid last := by
  induction run with
  | nil => exact valid
  | call _ middleValid resources key relation =>
    exact attach_valid _ middleValid resources key relation

theorem run_extends [DecidableEq B] {first last : Store B}
    (run : Run first last) : NativeValuePorts.Extends first.entries last.entries := by
  induction run with
  | nil => exact NativeValuePorts.extends_refl _
  | call _ valid resources key relation ih =>
    exact NativeValuePorts.extends_trans ih (attach_old _ valid resources key relation)

/-- A frozen source head or its already-read next cursor keeps the exact
ordered physical entries after every actual represented table mutation. -/
theorem run_captured_cursor [DecidableEq B] {first last : Store B}
    (run : Run first last) (valid : Valid first) (cursor : Option Nat)
    (bounded : ∀ index, cursor = some index → index < first.entries.length) :
    walk last.entries (run_valid run valid).backward cursor =
      walk first.entries valid.backward cursor :=
  walk_extends valid.backward (run_valid run valid).backward (run_extends run) cursor bounded

theorem run_captured_head [DecidableEq B] {first last : Store B}
    (run : Run first last) (valid : Valid first) (source : B) :
    walk last.entries (run_valid run valid).backward (first.heads source) =
      walk first.entries valid.backward (first.heads source) :=
  run_captured_cursor run valid (first.heads source) (head_bounded valid source)

theorem run_fiber_prefix [DecidableEq B] {first last : Store B}
    (run : Run first last) (valid : Valid first) (key : B) :
    ∃ added, fibers last (run_valid run valid) key = added ++ fibers first valid key := by
  induction run with
  | nil => exact ⟨[], rfl⟩
  | call past middleValid resources target relation ih =>
    obtain ⟨earlier, before⟩ := ih
    obtain ⟨added, after⟩ := attach_fiber_prefix _ middleValid resources target relation key
    exact ⟨added ++ earlier, by rw [after, before, List.append_assoc]⟩

theorem run_preserves_fiber [DecidableEq B] {first last : Store B}
    (run : Run first last) (valid : Valid first) (key : B) (relation : Nat)
    (old : relation ∈ fibers first valid key) :
    relation ∈ fibers last (run_valid run valid) key := by
  obtain ⟨added, same⟩ := run_fiber_prefix run valid key
  rw [same]
  exact List.mem_append_right added old

/-- Every cursor read keeps the full addressed entry and its complete bound
key, not merely membership of its endpoint pair in a projected graph. -/
theorem walk_entry_key {s : Store B} (valid : Valid s) (key : B)
    (cursor : Option Nat)
    (named : ∀ index, cursor = some index →
      ∃ entry : Entry B, s.entries[index]? = some entry ∧ entry.key = key) :
    ∀ item ∈ walk s.entries valid.backward cursor,
      s.entries[item.1]? = some item.2 ∧ item.2.key = key := by
  cases cursor with
  | none =>
    intro item member
    rw [walk_none] at member
    exact False.elim (List.not_mem_nil member)
  | some index =>
    obtain ⟨entry, found, same⟩ := named index rfl
    rw [walk_some _ _ found]
    intro item member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨found, same⟩
    · apply walk_entry_key valid key entry.previous _ item later
      intro previous link
      obtain ⟨old, stored, agrees⟩ := valid.links index entry previous found link
      exact ⟨old, stored, agrees.trans same⟩
termination_by cursorRank cursor
decreasing_by
  subst cursor
  cases previous : entry.previous with
  | none => simp [cursorRank]
  | some old =>
    have earlier := valid.backward index entry found old previous
    simp only [cursorRank]
    omega

theorem captured_head_entries [DecidableEq B] {first last : Store B}
    (run : Run first last) (valid : Valid first) (source : B)
    (item : Nat × Entry B)
    (member : item ∈ walk last.entries (run_valid run valid).backward (first.heads source)) :
    item.1 < first.entries.length ∧
      first.entries[item.1]? = some item.2 ∧
      last.entries[item.1]? = some item.2 ∧ item.2.key = source := by
  rw [run_captured_head run valid source] at member
  obtain ⟨found, named⟩ := walk_entry_key valid source (first.heads source)
    (valid.heads source) item member
  exact ⟨(List.getElem?_eq_some_iff.mp found).1, found,
    run_extends run _ _ found, named⟩

structure CursorState (B : Type) where
  store : Store B
  valid : Valid store
  cursor : Option Nat

/-- One cursor control advance in candidate_transfer_bound_origins: read
the old entry and capture its next pointer before any body attachments.
The body is a finite sequence of the represented actual table calls. Its
interner, dependency/evidence operations and errors are separate owners. -/
def CursorAdvance [DecidableEq B] (before after : CursorState B) : Prop :=
  ∃ (index : Nat) (entry : Entry B), before.cursor = some index ∧
    before.store.entries[index]? = some entry ∧ after.cursor = entry.previous ∧
    Run before.store after.store

theorem cursor_advance_decreases [DecidableEq B] {before after : CursorState B}
    (step : CursorAdvance before after) : cursorRank after.cursor < cursorRank before.cursor := by
  obtain ⟨index, entry, cursor, found, next, _⟩ := step
  rw [cursor, next]
  cases previous : entry.previous with
  | none => simp [cursorRank]
  | some old =>
    have earlier := before.valid.backward index entry found old previous
    simp only [cursorRank]
    omega

/-- Accessibility of this actual linked-loop control, even with arbitrarily
many newly attached target fibers between advances. This is not termination
of its body, the later metadata loop, a whole drain, or original inference. -/
theorem cursor_accessible [DecidableEq B] (start : CursorState B) :
    Acc (fun next previous => CursorAdvance previous next) start := by
  have wellFounded : WellFounded (fun next previous : CursorState B =>
      CursorAdvance previous next) :=
    Subrelation.wf (fun step => cursor_advance_decreases step)
      (InvImage.wf (fun state : CursorState B => cursorRank state.cursor) Nat.lt_wfRel.wf)
  exact wellFounded.apply start

structure Physical (B : Type) where
  native : NativeRelationInterner.Native
  fibers : Store B

structure PublicationResources where
  interner : NativeRelationInterner.Resources
  dependency : Bool
  evidence : Bool
  attachment : Resources
  sample : Bool

inductive PublicationOutcome where
  | complete (relation : Nat)
  | internerFailure (failure : NativeRelationInterner.Failure)
  | dependencyFailure
  | evidenceFailure
  | attachmentFailure (relation : Nat)
  | sampleFailure (relation : Nat)
  deriving DecidableEq, Repr

/-- Physical suffix of transport_witness_with_evidence after the earlier
snapshot and complete key construction: actual relation interning, dependency
publication, evidence transform, attachment, then sampling. The booleans are
observed results of the named external operations; their internal tables are
not modeled or asserted unchanged. Failures retain partial physical writes. -/
def publish [DecidableEq B] (state : Physical B) (valid : Valid state.fibers)
    (resources : PublicationResources) (target : B) (key : NativeValuePorts.Key) :
    Physical B × PublicationOutcome :=
  let called := state.native.call resources.interner key
  let afterCall : Physical B := ⟨called.1, state.fibers⟩
  match called.2 with
  | .error failure => (afterCall, .internerFailure failure)
  | .ok relation =>
    if resources.dependency = false then (afterCall, .dependencyFailure)
    else if resources.evidence = false then (afterCall, .evidenceFailure)
    else
      let attached := attach state.fibers valid resources.attachment target relation
      let afterAttach : Physical B := ⟨called.1, attached.1⟩
      if attached.2 = .exhausted then (afterAttach, .attachmentFailure relation)
      else if resources.sample = false then (afterAttach, .sampleFailure relation)
      else (afterAttach, .complete relation)

theorem publish_native [DecidableEq B] (state : Physical B) (valid : Valid state.fibers)
    (resources : PublicationResources) (target : B) (key : NativeValuePorts.Key) :
    (publish state valid resources target key).1.native =
      (state.native.call resources.interner key).1 := by
  cases called : (state.native.call resources.interner key).2 with
  | error failure => simp only [publish, called]
  | ok relation =>
    simp only [publish, called]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl

theorem publish_fiber_run [DecidableEq B] (state : Physical B) (valid : Valid state.fibers)
    (resources : PublicationResources) (target : B) (key : NativeValuePorts.Key) :
    Run state.fibers (publish state valid resources target key).1.fibers := by
  cases called : (state.native.call resources.interner key).2 with
  | error failure =>
    simp only [publish, called]
    exact .nil _
  | ok relation =>
    simp only [publish, called]
    split
    · exact .nil _
    · split
      · exact .nil _
      · split
        · exact .call (.nil _) valid resources.attachment target relation
        · split <;> exact .call (.nil _) valid resources.attachment target relation

theorem publish_valid [DecidableEq B] (state : Physical B) (valid : Valid state.fibers)
    (resources : PublicationResources) (target : B) (key : NativeValuePorts.Key) :
    Valid (publish state valid resources target key).1.fibers :=
  run_valid (publish_fiber_run state valid resources target key) valid

theorem publish_complete [DecidableEq B] (state : Physical B) (valid : Valid state.fibers)
    (resources : PublicationResources) (target : B) (key : NativeValuePorts.Key)
    {relation : Nat} (normal : (publish state valid resources target key).2 = .complete relation) :
    (state.native.call resources.interner key).2 = .ok relation ∧
    (attach state.fibers valid resources.attachment target relation).2 = .complete ∧
    (publish state valid resources target key).1.fibers =
      (attach state.fibers valid resources.attachment target relation).1 := by
  cases called : (state.native.call resources.interner key).2 with
  | error failure => simp [publish, called] at normal
  | ok found =>
    by_cases dependency : resources.dependency = false
    · simp [publish, called, dependency] at normal
    · by_cases evidence : resources.evidence = false
      · simp [publish, called, dependency, evidence] at normal
      · cases attached : (attach state.fibers valid resources.attachment target found).2 with
        | exhausted => simp [publish, called, dependency, evidence, attached] at normal
        | complete =>
          by_cases sampled : resources.sample = false
          · simp [publish, called, dependency, evidence, attached, sampled] at normal
          · have same : found = relation := by
              simpa [publish, called, dependency, evidence, attached, sampled] using normal
            subst relation
            exact ⟨rfl, attached, by
              simp [publish, called, dependency, evidence, attached, sampled]⟩

/-- One computed physical suffix supplies the SAME raw relation ID in the
actual materialized native interner and the target's actual linked fibers.
All fields of the complete Key, including deferred Function demand, survive. -/
theorem published_fiber_exact [DecidableEq B] (state : Physical B) (valid : Valid state.fibers)
    (history : NativeRelationInterner.NativeHistory state.native)
    (resources : PublicationResources) (target : B) (key : NativeValuePorts.Key)
    {relation : Nat} (normal : (publish state valid resources target key).2 = .complete relation) :
    NativeValuePorts.Allowed key ∧
      (publish state valid resources target key).1.native.store.readback relation = some key ∧
      relation ∈ fibers (publish state valid resources target key).1.fibers
        (publish_valid state valid resources target key) target := by
  obtain ⟨called, attached, same⟩ := publish_complete state valid resources target key normal
  have stored := NativeRelationInterner.native_ok_refines_arena history called [] []
  refine ⟨stored.1, ?_, ?_⟩
  · rw [publish_native]
    exact stored.2.2.1
  · have supplied := attach_supplies_relation state.fibers valid resources.attachment
      target relation attached
    simpa only [same] using supplied

/-- Even an error after interning or attachment cannot alter the captured
old source chain in this physical projection. Whole rollback is outside it. -/
theorem publish_captured_source [DecidableEq B] (state : Physical B) (valid : Valid state.fibers)
    (resources : PublicationResources) (target source : B) (key : NativeValuePorts.Key) :
    walk (publish state valid resources target key).1.fibers.entries
      (publish_valid state valid resources target key).backward (state.fibers.heads source) =
      walk state.fibers.entries valid.backward (state.fibers.heads source) :=
  run_captured_head (publish_fiber_run state valid resources target key) valid source

end YulangClosure.OriginalBoundFibers
