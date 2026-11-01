import Std

/-!
R139: a finite, snapshot-local identity table, independent of native encoding.
The seven payload types retain complete identity values, rather than replacing
them with source offsets or hashes. Instantiating their equality with Rust Eq,
using one table for both inventories, and the R136 native bridge remain open.
No code from distinct snapshots is compared here. Failure exposes only an
error, even when a private prefix has already been constructed.
-/
namespace YulangClosure.FormalPermissionIdentityEncodingR139

inductive TaggedKey (Owner Occurrence Formal Scope Node Effect Symbol : Type) where
  | owner : Owner → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | occurrence : Occurrence → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | formal : Formal → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | scope : Scope → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | node : Node → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | effect : Effect → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | symbol : Symbol → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  deriving DecidableEq

variable {K : Type} [DecidableEq K]

abbrev Table (K : Type) := List K

def resolve (table : Table K) (key : K) : Option Nat :=
  if key ∈ table then some (table.idxOf key) else none

def register (table : Table K) (key : K) : Table K × Nat :=
  if key ∈ table then (table, table.idxOf key)
  else (table ++ [key], table.length)

theorem equal_keys_resolve (table : Table K) (a b : K) (same : a = b) :
    resolve table a = resolve table b := by
  cases same
  rfl

theorem registered_index_injective (table : Table K) (a b : K)
    (ha : a ∈ table) (hb : b ∈ table)
    (same : table.idxOf a = table.idxOf b) : a = b := by
  have ea : table[table.idxOf a]? = some a :=
    List.getElem?_eq_some_iff.mpr
      ⟨List.idxOf_lt_length_of_mem ha, List.getElem_idxOf (List.idxOf_lt_length_of_mem ha)⟩
  have eb : table[table.idxOf b]? = some b :=
    List.getElem?_eq_some_iff.mpr
      ⟨List.idxOf_lt_length_of_mem hb, List.getElem_idxOf (List.idxOf_lt_length_of_mem hb)⟩
  rw [same] at ea
  exact Option.some.inj (ea.symm.trans eb)

theorem distinct_registered_codes (table : Table K) (a b : K) (n : Nat)
    (ea : resolve table a = some n) (eb : resolve table b = some n) : a = b := by
  by_cases ha : a ∈ table
  · by_cases hb : b ∈ table
    · apply registered_index_injective table a b ha hb
      have ia : table.idxOf a = n := by simpa [resolve, ha] using ea
      have ib : table.idxOf b = n := by simpa [resolve, hb] using eb
      exact ia.trans ib.symm
    · simp [resolve, hb] at eb
  · simp [resolve, ha] at ea

theorem append_preserves (table suffix : Table K) (key : K) (n : Nat)
    (old : resolve table key = some n) : resolve (table ++ suffix) key = some n := by
  by_cases h : key ∈ table
  · simpa [resolve, h, List.idxOf_append] using old
  · simp [resolve, h] at old

theorem register_reuses (table : Table K) (key : K) (h : key ∈ table) :
    register table key = (table, table.idxOf key) := by
  simp [register, h]

theorem register_fresh (table : Table K) (key : K) (h : key ∉ table) :
    register table key = (table ++ [key], table.length) := by
  simp [register, h]

theorem register_resolves (table : Table K) (key : K) :
    resolve (register table key).1 key = some (register table key).2 := by
  by_cases h : key ∈ table
  · simp [register, resolve, h]
  · simp [register, resolve, h, List.idxOf_append]

theorem register_preserves (table : Table K) (key oldKey : K) (n : Nat)
    (old : resolve table oldKey = some n) :
    resolve (register table key).1 oldKey = some n := by
  by_cases h : key ∈ table
  · simpa [register, h] using old
  · simpa [register, h] using append_preserves table [key] oldKey n old

def extend (table : Table K) : List K → Table K
  | [] => table
  | key :: keys => extend (register table key).1 keys

theorem extend_preserves (keys : List K) (table : Table K) (key : K) (n : Nat)
    (old : resolve table key = some n) : resolve (extend table keys) key = some n := by
  induction keys generalizing table with
  | nil => exact old
  | cons head tail ih =>
      exact ih (register table head).1 (register_preserves table head key n old)

theorem extend_registers (keys : List K) (table : Table K) (key : K)
    (member : key ∈ keys) : ∃ n, resolve (extend table keys) key = some n := by
  induction keys generalizing table with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst key
        exact ⟨(register table head).2,
          extend_preserves tail (register table head).1 head _ (register_resolves table head)⟩
      · exact ih (register table head).1 later

/-- Encode only against one completed table. Its registration obligations are
proved below for every member of the input sequence, including repetitions. -/
def encode (table : Table K) (keys : List K) : List Nat := keys.map table.idxOf

theorem encode_length (table : Table K) (keys : List K) :
    (encode table keys).length = keys.length := by
  simp [encode]

theorem encode_position (table : Table K) (keys : List K) (i : Nat) :
    (encode table keys)[i]? = keys[i]?.map table.idxOf := by
  simp [encode]

theorem encode_append (table : Table K) (left right : List K) :
    encode table (left ++ right) = encode table left ++ encode table right := by
  simp [encode]

theorem encode_duplicates (table : Table K) (key : K) (count : Nat) :
    encode table (List.replicate count key) = List.replicate count (table.idxOf key) := by
  simp [encode]

theorem completed_sequence_resolves (keys : List K) (key : K) (member : key ∈ keys) :
    resolve (extend [] keys) key = some ((extend [] keys).idxOf key) := by
  obtain ⟨n, found⟩ := extend_registers keys [] key member
  by_cases h : key ∈ extend [] keys
  · simp [resolve, h]
  · simp [resolve, h] at found

/-- The only snapshot constructor used by `construct` is the successful final
branch. An error carries no table, codes, snapshot, or partial-success payload. -/
structure Snapshot (K : Type) where
  table : Table K
  codes : List Nat

inductive Failure where
  | reservation
  | lookup
  deriving DecidableEq

def constructFrom (reserve : K → Bool) (table : Table K) :
    List K → Except Failure (Snapshot K)
  | [] => .ok ⟨table, []⟩
  | key :: keys =>
      if reserve key then
        let registered := register table key
        match constructFrom reserve registered.1 keys with
        | .error error => .error error
        | .ok snapshot =>
            match resolve snapshot.table key with
            | none => .error .lookup
            | some code => .ok ⟨snapshot.table, code :: snapshot.codes⟩
      else .error .reservation

def construct (reserve : K → Bool) (keys : List K) : Except Failure (Snapshot K) :=
  constructFrom reserve [] keys

def authenticated : Except Failure (Snapshot K) → Option (Snapshot K)
  | .error _ => none
  | .ok snapshot => some snapshot

theorem failure_has_no_snapshot (reserve : K → Bool) (keys : List K) (error : Failure)
    (failed : construct reserve keys = .error error) :
    authenticated (construct reserve keys) = none := by
  rw [failed]
  rfl

theorem failure_cannot_authenticate (error : Failure) (snapshot : Snapshot K) :
    authenticated (.error error) ≠ some snapshot := by
  simp [authenticated]

theorem reservation_failure (reserve : K → Bool) (table : Table K)
    (key : K) (keys : List K) (failed : reserve key = false) :
    constructFrom reserve table (key :: keys) = .error .reservation := by
  simp [constructFrom, failed]

theorem suffix_failure_discards_prefix (reserve : K → Bool) (table : Table K)
    (key : K) (keys : List K) (error : Failure) (allowed : reserve key = true)
    (failed : constructFrom reserve (register table key).1 keys = .error error) :
    constructFrom reserve table (key :: keys) = .error error := by
  simp [constructFrom, allowed, failed]

end YulangClosure.FormalPermissionIdentityEncodingR139


-- Complete direct theorem type and transitive axiom audit.
#check @YulangClosure.FormalPermissionIdentityEncodingR139.equal_keys_resolve
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.equal_keys_resolve
#check @YulangClosure.FormalPermissionIdentityEncodingR139.registered_index_injective
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.registered_index_injective
#check @YulangClosure.FormalPermissionIdentityEncodingR139.distinct_registered_codes
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.distinct_registered_codes
#check @YulangClosure.FormalPermissionIdentityEncodingR139.append_preserves
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.append_preserves
#check @YulangClosure.FormalPermissionIdentityEncodingR139.register_reuses
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.register_reuses
#check @YulangClosure.FormalPermissionIdentityEncodingR139.register_fresh
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.register_fresh
#check @YulangClosure.FormalPermissionIdentityEncodingR139.register_resolves
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.register_resolves
#check @YulangClosure.FormalPermissionIdentityEncodingR139.register_preserves
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.register_preserves
#check @YulangClosure.FormalPermissionIdentityEncodingR139.extend_preserves
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.extend_preserves
#check @YulangClosure.FormalPermissionIdentityEncodingR139.extend_registers
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.extend_registers
#check @YulangClosure.FormalPermissionIdentityEncodingR139.encode_length
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.encode_length
#check @YulangClosure.FormalPermissionIdentityEncodingR139.encode_position
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.encode_position
#check @YulangClosure.FormalPermissionIdentityEncodingR139.encode_append
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.encode_append
#check @YulangClosure.FormalPermissionIdentityEncodingR139.encode_duplicates
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.encode_duplicates
#check @YulangClosure.FormalPermissionIdentityEncodingR139.completed_sequence_resolves
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.completed_sequence_resolves
#check @YulangClosure.FormalPermissionIdentityEncodingR139.failure_has_no_snapshot
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.failure_has_no_snapshot
#check @YulangClosure.FormalPermissionIdentityEncodingR139.failure_cannot_authenticate
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.failure_cannot_authenticate
#check @YulangClosure.FormalPermissionIdentityEncodingR139.reservation_failure
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.reservation_failure
#check @YulangClosure.FormalPermissionIdentityEncodingR139.suffix_failure_discards_prefix
#print axioms YulangClosure.FormalPermissionIdentityEncodingR139.suffix_failure_discards_prefix
