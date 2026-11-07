import Yulang.CommonSymbolicBoundRigid

/-!
# Finite query support of fixed-bound inspection

Required and optional references must occur in the supplied query inventory.
Original shared IDs and the three constants need no query entry. The only
additional query introduced by default inspection is the same label with
top payload; `TopClosed` states exactly that finite closure requirement.

All support results are syntactic and independent of row/value assignments,
constructor equations, successful inference, or a worklist. They establish
one inspection step, not closure of arbitrary future graph expansion.
-/

namespace Yulang.CommonSymbolicBoundSupport

open CommonSymbolicBoundInspection
open CommonSymbolicConstraints (Check Branch)
open CommonPayloadProjection (Payload)

universe u v

abbrev Query (Node : Type v) := Nat × Option Node

def Supported (queries : List (Query Node)) : BoundRef Node → Prop
  | .required label payload | .optional label payload => (label, payload) ∈ queries
  | _ => True

@[simp] theorem supported_original (queries : List (Query Node)) (node : Node) :
    Supported queries (.original node) := trivial

@[simp] theorem supported_top (queries : List (Query Node)) : Supported queries .top := trivial
@[simp] theorem supported_width (queries : List (Query Node)) : Supported queries .width := trivial
@[simp] theorem supported_exactEmpty (queries : List (Query Node)) :
    Supported queries .exactEmpty := trivial

@[simp] theorem supported_required (queries : List (Query Node)) (label : Nat) (payload : Option Node) :
    Supported queries (.required label payload) ↔ (label, payload) ∈ queries := Iff.rfl

@[simp] theorem supported_optional (queries : List (Query Node)) (label : Nat) (payload : Option Node) :
    Supported queries (.optional label payload) ↔ (label, payload) ∈ queries := Iff.rfl

def TopClosed (queries : List (Query Node)) : Prop :=
  ∀ label payload, (label, payload) ∈ queries → (label, none) ∈ queries

@[simp] theorem payloadRef_supported (queries : List (Query Node)) (payload : Option Node) :
    Supported queries (payloadRef payload) := by
  cases payload <;> trivial

@[simp] def RigidSupported (queries : List (Query Node)) : Rigid Rows Node → Prop
  | .pair first last => Supported queries first ∧ Supported queries last
  | .variant _ payload => Supported queries payload
  | .arrow input _ output _ => Supported queries input ∧ Supported queries output
  | _ => True

@[simp] def SourceSupported (queries : List (Query Node)) : Source Rows Node → Prop
  | .reference node => Supported queries node
  | .union first last | .record _ first last | .recordDefault _ first last =>
      Supported queries first ∧ Supported queries last
  | .rigid node => RigidSupported queries node
  | _ => True

/-- The output grammar itself excludes profiles, dynamic flags, and
compound payload syntax in addition to checking the finite query inventory. -/
@[simp] def CheckSupported (queries : List (Query Node)) : Check Rows Node (BoundRef Node) → Prop
  | .childBelow (.ref source) (.ref target) => Supported queries source ∧ Supported queries target
  | .rowBelow _ _ => True
  | .flag (.literal _) => True
  | _ => False

def BranchSupported (queries : List (Query Node)) (branch : Branch Rows Node (BoundRef Node)) : Prop :=
  ∀ check ∈ branch, CheckSupported queries check

def OutputSupported (queries : List (Query Node)) (output : Output Rows Node) : Prop :=
  ∀ branch ∈ output, BranchSupported queries branch

theorem supported_plain (queries : List (Query Node)) (output : Output Rows Node)
    (supported : OutputSupported queries output) : Plain output := by
  intro branch member check included
  have allowed := supported branch member check included
  cases check with
  | childBelow source target =>
      cases source <;> cases target <;> simp_all [PlainCheck]
  | rowBelow => trivial
  | flag expression => cases expression <;> simp_all [PlainCheck]
  | profileBelow => cases allowed

theorem default_branches_supported (queries : List (Query Node)) (closed : TopClosed queries)
    (label : Nat) (source fallback : BoundRef Node) (payload : Option Node)
    (sourceSupported : Supported queries source) (fallbackSupported : Supported queries fallback)
    (selected : (label, payload) ∈ queries) :
    OutputSupported (Rows := Rows) queries (defaultBranches label source fallback payload) := by
  have top := closed label payload selected
  simp [OutputSupported, BranchSupported, defaultBranches, edge,
    sourceSupported, fallbackSupported, selected, top]

theorem inspect_required_supported (queries : List (Query Node)) (closed : TopClosed queries)
    (source : Source Rows Node) (label : Nat) (payload : Option Node)
    (sourceSupported : SourceSupported queries source) (selected : (label, payload) ∈ queries) :
    OutputSupported queries (inspectRequired source label payload) := by
  cases source with
  | reference | union =>
      simp_all [inspectRequired, OutputSupported, BranchSupported, edge]
  | width | exactEmpty => simp [inspectRequired, OutputSupported]
  | record current head tail =>
      by_cases same : label = current <;>
        simp_all [inspectRequired, OutputSupported, BranchSupported, edge]
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        simp only [inspectRequired, ↓reduceIte]
        exact default_branches_supported queries closed label base fallback payload
          sourceSupported.1 sourceSupported.2 selected
      · simp_all [inspectRequired, OutputSupported, BranchSupported, edge]
  | rigid node => cases node <;> simp [inspectRequired, OutputSupported, BranchSupported]

theorem inspect_optional_supported (queries : List (Query Node)) (closed : TopClosed queries)
    (source : Source Rows Node) (label : Nat) (payload : Option Node)
    (sourceSupported : SourceSupported queries source) (selected : (label, payload) ∈ queries) :
    OutputSupported queries (inspectOptional source label payload) := by
  cases source with
  | reference | union =>
      simp_all [inspectOptional, OutputSupported, BranchSupported, edge]
  | width | exactEmpty => simp [inspectOptional, OutputSupported, BranchSupported]
  | record current head tail =>
      by_cases same : label = current <;>
        simp_all [inspectOptional, OutputSupported, BranchSupported, edge]
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        simp only [inspectOptional, ↓reduceIte]
        exact default_branches_supported queries closed label base fallback payload
          sourceSupported.1 sourceSupported.2 selected
      · simp_all [inspectOptional, OutputSupported, BranchSupported, edge]
  | rigid node => cases node <;> simp [inspectOptional, OutputSupported, BranchSupported]

theorem inspect_width_supported (queries : List (Query Node)) (source : Source Rows Node)
    (sourceSupported : SourceSupported queries source) :
    OutputSupported queries (inspectWidth source) := by
  cases source with
  | reference | union => simp_all [inspectWidth, OutputSupported, BranchSupported, edge]
  | width | exactEmpty | record | recordDefault => simp [inspectWidth, OutputSupported, BranchSupported]
  | rigid node => cases node <;> simp [inspectWidth, OutputSupported, BranchSupported]

theorem inspect_rigid_supported (queries : List (Query Node))
    (source : Source Rows Node) (target : Rigid Rows Node) (targetRef : BoundRef Node)
    (sourceSupported : SourceSupported queries source)
    (targetSupported : RigidSupported queries target) (referenceSupported : Supported queries targetRef) :
    OutputSupported queries (inspectRigid source target targetRef) := by
  cases source with
  | reference | union => simp_all [inspectRigid, OutputSupported, BranchSupported, edge]
  | rigid node =>
      cases node <;> cases target <;>
        simp_all [inspectRigid, CommonSymbolicRigidInspection.inspect, OutputSupported, BranchSupported]
  | width | exactEmpty | record | recordDefault =>
      cases target <;> simp [inspectRigid, OutputSupported, BranchSupported]

/-- Arrow rows are copied literally, with the original variance directions.
The fixed-bound extension introduces no row reference or row renaming. -/
theorem inspect_arrow_syntax (input output input' output' : BoundRef Node)
    (incoming outgoing incoming' outgoing' : Rows) (targetRef : BoundRef Node) :
    inspectRigid (.rigid (.arrow input incoming output outgoing))
        (.arrow input' incoming' output' outgoing') targetRef =
      [[edge input' input, .rowBelow incoming' incoming,
        edge output output', .rowBelow outgoing outgoing']] := rfl

end Yulang.CommonSymbolicBoundSupport
