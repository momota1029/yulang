import Yulang.GeneralDeclarativeWitnessOrigins350
import Yulang.GeneralDeclarativeWitnessRecordWhole350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessIdentity351
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralSourceState (Output)

/-- A version is scoped to a particular occurrence and one ordered compiler
write. Position and logical target are independent fields. -/
structure Key where
  path : List Nat
  role : Nat
  version : Nat
  write : Nat
  target : Nat
  deriving DecidableEq

structure Owned where
  key : Key
  equation : Equation
  deriving DecidableEq

structure Stamp where
  path : List Nat
  role : Nat
  version : Nat
  deriving DecidableEq

def identify (publisher : Stamp) (index : Nat) (e : Equation) : Owned :=
  ⟨⟨publisher.path,publisher.role,publisher.version,index,e.left⟩,e⟩

/-- Exact coordinates from the compiler's ordered write trace. A
certificate cannot provide a row by matching only its value or target. -/
def select (trace : List Fixed) (publisher : Stamp) (ordinal : Nat) :
    Option Owned := do
  let block ← trace.find? (fun f => decide (f.path = publisher.path ∧ f.demand.role = publisher.role))
  let row ← block.equations[ordinal]?
  pure (identify publisher ordinal row)

theorem select_sound {trace : List Fixed} {publisher : Stamp} {ordinal : Nat} {row : Owned}
    (found : select trace publisher ordinal = some row) :
    ∃ f ∈ trace, f.path = publisher.path ∧ f.demand.role = publisher.role ∧
      f.equations[ordinal]? = some row.equation ∧
      row.key = ⟨publisher.path,publisher.role,publisher.version,ordinal,row.equation.left⟩ := by
  unfold select at found
  cases hit : trace.find? (fun f => decide (f.path = publisher.path ∧ f.demand.role = publisher.role)) with
  | none => rw [hit] at found; cases found
  | some f =>
    rw [hit] at found
    cases position : f.equations[ordinal]? with
    | none => simp [position] at found
    | some e =>
      have named : identify publisher ordinal e = row := by simpa [position] using found
      cases named
      have seen := List.find?_some hit
      have exactFields : f.path = publisher.path ∧ f.demand.role = publisher.role := of_decide_eq_true seen
      exact ⟨f,List.mem_of_find?_eq_some hit,exactFields.1,exactFields.2,position,rfl⟩

/-- Names fed to the existing semantics are the indices in a single fixed
catalogue. Release is matched on the complete occurrence/version key,
never on type equality, obligation role alone, or a reused target. -/
def table (source : List Equation) (owned : List Owned) (released : List Key) : Table :=
  let spots := owned.zipIdx
  ⟨source,spots.map (fun (ref,i) => (ref.equation,i)),
    (spots.filter (fun (ref,_) => released.contains ref.key)).map Prod.snd⟩

def unique (owned : List Owned) : Bool := decide ((owned.map Owned.key).Nodup)

theorem writer {owned : List Owned} (entries : owned[idx]? = some row) :
    (row.equation,idx) ∈ (table source owned released).produced := by
  refine List.mem_map.mpr ⟨(row,idx),?_,rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr entries

theorem release_exact {owned : List Owned} {released : List Key} {row : Owned}
    (entry : owned[idx]? = some row) :
    idx ∈ (table source owned released).released ↔ row.key ∈ released := by
  constructor
  · intro mem
    obtain ⟨⟨x,i⟩,site,equal⟩ := List.mem_map.mp mem
    cases equal
    obtain ⟨hereAt,allowed⟩ := List.mem_filter.mp site
    have here := List.mk_mem_zipIdx_iff_getElem?.mp hereAt
    cases Option.some.inj (here.symm.trans entry)
    simpa using allowed
  · intro allowed
    exact List.mem_map.mpr ⟨(row,idx),List.mem_filter.mpr
      ⟨List.mk_mem_zipIdx_iff_getElem?.mpr entry,by simpa using allowed⟩,rfl⟩

end Yulang.GeneralDeclarativeWitnessIdentity351
