import Yulang.GeneralObservedMetadataCanonical290

/-! Explicit data for resolved catalogue inputs. Flags are exclusive by
construction and do not imply that their layouts are materializable. -/
namespace Yulang.GeneralSourceMetadataRows291
open GeneralDeclarationPatterns (Constructor Constructors ParameterKind)
open GeneralCandidateInspection (Primitive Primitives)
open GeneralNominalInspection (Interpretation)
open GeneralObservedMetadataOverlay290 (overlay default_outside)

inductive DefaultCode
  | absent
  | identityEmptyLayout
  deriving DecidableEq, Repr

def DefaultCode.decode : DefaultCode → Constructors
  | .absent => fun _ => none
  | .identityEmptyLayout => fun key => some ⟨[],key⟩

inductive Class
  | primitive (kind : Primitive)
  | invariant
  | unclassified

def Class.primitiveValue : Class → Option Primitive
  | .primitive kind => some kind
  | _ => none

def Class.invariantFlag : Class → Bool
  | .invariant => true
  | _ => false

structure Row where
  key : Nat
  ctor : Option Constructor
  classification : Class

structure Source where
  fallback : DefaultCode
  rows : List Row

def constructorRows (s : Source) : List (Nat × Option Constructor) :=
  s.rows.map fun row => (row.key,row.ctor)

def primitiveRows (s : Source) : List (Nat × Option Primitive) :=
  s.rows.map fun row => (row.key,row.classification.primitiveValue)

def invariantRows (s : Source) : List (Nat × Bool) :=
  s.rows.map fun row => (row.key,row.classification.invariantFlag)

def constructors (s : Source) : Constructors := overlay s.fallback.decode (constructorRows s)
def primitives (s : Source) : Primitives := overlay (fun _ => none) (primitiveRows s)
def invariants (s : Source) : Nat → Bool := overlay (fun _ => false) (invariantRows s)

theorem exclusive (rows : List Row) (key : Nat) :
    invariants ⟨.absent,rows⟩ key = true → primitives ⟨.absent,rows⟩ key = none := by
  induction rows with
  | nil => simp [invariants,invariantRows,overlay]
  | cons row rows ih =>
    by_cases found : key = row.key
    · cases row with
      | mk n ctor c => cases c <;> simp [invariants,invariantRows,primitives,primitiveRows,overlay,found,Class.invariantFlag,Class.primitiveValue]
    · simpa [invariants,invariantRows,primitives,primitiveRows,overlay,found] using ih

def interpretation (s : Source) : Interpretation :=
  ⟨primitives s,invariants s,fun key h => exclusive s.rows key h⟩

theorem interpretation_ext (i j : Interpretation)
    (p : i.primitives = j.primitives) (n : i.invariantNominal = j.invariantNominal) : i = j := by
  cases i
  cases j
  cases p
  cases n
  rfl

theorem outside_constructor (s : Source) (key : Nat) (h : key ∉ s.rows.map Row.key) :
    constructors s key = s.fallback.decode key := by
  apply default_outside
  simpa only [constructorRows,List.map_map,Function.comp_def] using h

theorem outside_primitive (s : Source) (key : Nat) (h : key ∉ s.rows.map Row.key) :
    primitives s key = none := by
  apply default_outside
  simpa only [primitiveRows,List.map_map,Function.comp_def] using h

theorem outside_invariant (s : Source) (key : Nat) (h : key ∉ s.rows.map Row.key) :
    invariants s key = false := by
  apply default_outside
  simpa only [invariantRows,List.map_map,Function.comp_def] using h

end Yulang.GeneralSourceMetadataRows291
