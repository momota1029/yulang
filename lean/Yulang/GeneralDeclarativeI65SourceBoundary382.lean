import Yulang.GeneralDeclarativeI65OrdinaryAttachment382
import Yulang.GeneralDeclarativeI65CommitAuthority382

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeWitnessNativeInstall360 (World)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)

/-- One caller-supplied boundary context. The attachment and equality
only link ordinary rows and the physical world to the same current
state. Their types neither manufacture nor authenticate a completion
list or native gate. Those manifests have to be sourced independently
at the actual entry point, not selected by an existential inside a rule. -/
structure SourceBoundary382 (s : State) where
  ledger : Table
  ordinary : Attached s.current.ordinary ledger
  world : World
  current : world.ordinary = s.current.ordinary
  gate : ReleaseAuthority

inductive PrimitiveKey382 where
  | ordinary (row : Equation)
  | native (written : Write) (logical : Nat)

/-- Data-bearing proof of a primitive observation in exactly one
boundary context. Hard separation of directly authored rows,
completed ordinary outputs, and native literal releases. Nothing
here constitutes a role match or election. -/
inductive PrimitiveRead382 {s : State} (c : SourceBoundary382 s) :
    PrimitiveKey382 → Type where
  | authored (row : Equation) : row ∈ c.ledger.authored → PrimitiveRead382 c (.ordinary row)
  | completed (row : Equation) (owner : Nat) :
      (row,owner) ∈ c.ledger.produced → owner ∈ c.ledger.released →
      PrimitiveRead382 c (.ordinary row)
  | native (written : Write) (logical : Nat) :
      RetainedPhysicalOrigin381 s c.world written logical →
      BoundNativeRead381 s c.world c.gate written →
      PrimitiveRead382 c (.native written logical)

theorem boundary_ordinary_read_iff382 {s : State} (c : SourceBoundary382 s) (row : Equation) :
    Nonempty (PrimitiveRead382 c (.ordinary row)) ↔
      row ∈ (restriction (support c.ordinary)).equations := by
  rw [ordinary_support_requires_actual_origin382]
  constructor
  · rintro ⟨observed⟩
    cases observed with
    | authored _ found => exact .inl found
    | completed _ owner output done => exact .inr ⟨owner,output,done⟩
  · rintro (direct|⟨owner,output,done⟩)
    · exact ⟨.authored row direct⟩
    · exact ⟨.completed row owner output done⟩

theorem boundary_native_read_iff382 {s : State} (c : SourceBoundary382 s)
    (written : Write) (logical : Nat) :
    Nonempty (PrimitiveRead382 c (.native written logical)) ↔
      RetainedPhysicalOrigin381 s c.world written logical ∧ written.address ∈ c.gate.grants := by
  constructor
  · rintro ⟨observed⟩
    cases observed with
    | native _ _ rail opened =>
      exact ⟨rail,(native_context_read_iff_its_grant381 rail).mp ⟨opened⟩⟩
  · rintro ⟨rail,grant⟩
    obtain ⟨opened⟩ := (native_context_read_iff_its_grant381 rail).mpr grant
    exact ⟨.native written logical rail opened⟩

/-- The list stores every occurrence in literal order. It does not
turn set membership or equality of values into identity of events. -/
inductive PrimitiveReads382 {s : State} (c : SourceBoundary382 s) :
    List PrimitiveKey382 → Type where
  | nil : PrimitiveReads382 c []
  | cons : PrimitiveRead382 c first → PrimitiveReads382 c rest → PrimitiveReads382 c (first::rest)

/-- This proposition describes availability of a fresh proof of each
indexed read, not uniqueness or reconstruction of an erased trace. -/
def PrimitiveAvailable382 {s : State} (c : SourceBoundary382 s) : PrimitiveKey382 → Prop
  | .ordinary row => row ∈ (restriction (support c.ordinary)).equations
  | .native written logical =>
      RetainedPhysicalOrigin381 s c.world written logical ∧ written.address ∈ c.gate.grants

theorem boundary_primitive_read_iff382 {s : State} (c : SourceBoundary382 s) (k : PrimitiveKey382) :
    Nonempty (PrimitiveRead382 c k) ↔ PrimitiveAvailable382 c k := by
  cases k with
  | ordinary row => exact boundary_ordinary_read_iff382 c row
  | native written logical => exact boundary_native_read_iff382 c written logical

theorem ordered_primitive_boundary_exact382 {s : State} (c : SourceBoundary382 s)
    (keys : List PrimitiveKey382) :
    Nonempty (PrimitiveReads382 c keys) ↔ ∀ k ∈ keys, PrimitiveAvailable382 c k := by
  induction keys with
  | nil => exact ⟨fun _ _ no => False.elim (List.not_mem_nil no),fun _ => ⟨.nil⟩⟩
  | cons first following ih =>
    constructor
    · rintro ⟨reads⟩ k found
      cases reads with
      | cons now later =>
        rcases List.mem_cons.mp found with rfl|after
        · exact (boundary_primitive_read_iff382 c k).mp ⟨now⟩
        · exact ih.mp ⟨later⟩ k after
    · intro all
      obtain ⟨now⟩ := (boundary_primitive_read_iff382 c first).mpr
        (all first List.mem_cons_self)
      obtain ⟨later⟩ := ih.mpr (fun k found => all k (List.mem_cons_of_mem _ found))
      exact ⟨.cons now later⟩

end Yulang.GeneralDeclarativeI65
