import Yulang.CommonRoleOpenDescent

/-! Concrete slots for a finite table of endpoint occurrences. This is a
source-identity-preserving table allocator, not a proof that a resolver's
entire dynamically generated endpoint universe fits this table. -/
namespace Yulang.CommonRoleEndpointSlots
open CommonRoleSettledSyntax

abbrev Table := List (Ty × Ty)
abbrev Source (table : Table) := Fin table.length × Bool

/-- A row and side, rather than Ty equality, determine source identity. -/
def allocate (table : Table) (source : Source table) : Fin (2 * table.length) :=
  ⟨2 * source.1.val + if source.2 then 1 else 0, by
    have bound := source.1.isLt
    split <;> omega⟩

def decode (table : Table) (slot : Fin (2 * table.length)) : Source table :=
  (⟨slot.val / 2, by have bound := slot.isLt; omega⟩, slot.val % 2 == 1)

@[simp] theorem decode_allocate (table : Table) (source : Source table) :
    decode table (allocate table source) = source := by
  rcases source with ⟨⟨row, bound⟩, side⟩
  cases side <;> simp [decode, allocate, Nat.add_div, Nat.mul_div_right]

@[simp] theorem allocate_decode (table : Table) (slot : Fin (2 * table.length)) :
    allocate table (decode table slot) = slot := by
  apply Fin.ext
  simp only [allocate, decode]
  by_cases h : slot.val % 2 = 1
  · simp only [h, BEq.rfl, ↓reduceIte]
    omega
  · have rem := Nat.mod_lt slot.val (by decide : 0 < 2)
    simp only [beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega

theorem allocate_injective (table : Table) (left right : Source table)
    (same : allocate table left = allocate table right) : left = right := by
  have h := congrArg (decode table) same
  simpa using h

/-- The original endpoint is retained verbatim, including opaque nominal names. -/
def endpoint (table : Table) (source : Source table) : Ty :=
  if source.2 then table[source.1.val].2 else table[source.1.val].1

def slotEndpoint (table : Table) (slot : Fin (2 * table.length)) : Ty :=
  endpoint table (decode table slot)

@[simp] theorem endpoint_preserved (table : Table) (source : Source table) :
    slotEndpoint table (allocate table source) = endpoint table source := by
  simp [slotEndpoint]

/-- No semantic interpretation is selected by the allocator. Whatever the
source interpretation is, transport to slots recovers it exactly. -/
def assignment (table : Table) (interpret : Ty → α) : Fin (2 * table.length) → α :=
  fun slot => interpret (slotEndpoint table slot)

theorem interpretation_preserved (table : Table) (interpret : Ty → α)
    (source : Source table) :
    assignment table interpret (allocate table source) = interpret (endpoint table source) := by
  simp [assignment]

theorem nominal_preserved (table : Table) (source : Source table) (name : Nat)
    (original : endpoint table source = .atom (.named name)) :
    slotEndpoint table (allocate table source) = .atom (.named name) := by
  simpa using original

theorem wrapped_nominal_preserved (table : Table) (source : Source table)
    (name : Nat) (payload : Ty)
    (original : endpoint table source = .wrap (.nominal name) payload) :
    slotEndpoint table (allocate table source) = .wrap (.nominal name) payload := by
  simpa using original

/-- Two different source occurrences never share a slot, even if their Ty
values happen to be equal. -/
theorem distinct_sources_distinct_slots (table : Table) (left right : Source table)
    (distinct : left ≠ right) : allocate table left ≠ allocate table right :=
  fun same => distinct (allocate_injective table left right same)

/-- Collect both endpoints of each actual request, preserving list positions. -/
def collect (requests : List CommonRoleOpenDescent.Request) : Table :=
  requests.map (fun request => (request.lower, request.upper))

def requestSource (requests : List CommonRoleOpenDescent.Request)
    (index : Fin requests.length) (upper : Bool) : Source (collect requests) :=
  (⟨index.val, by simp [collect]⟩, upper)

theorem request_lower_preserved (requests : List CommonRoleOpenDescent.Request)
    (index : Fin requests.length) :
    slotEndpoint (collect requests)
      (allocate (collect requests) (requestSource requests index false)) = requests[index.val].lower := by
  simp [endpoint, collect, requestSource]

theorem request_upper_preserved (requests : List CommonRoleOpenDescent.Request)
    (index : Fin requests.length) :
    slotEndpoint (collect requests)
      (allocate (collect requests) (requestSource requests index true)) = requests[index.val].upper := by
  simp [endpoint, collect, requestSource]

end Yulang.CommonRoleEndpointSlots
