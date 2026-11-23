import Yulang.CommonRecursiveNominalIntervalContext

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open CommonRecursiveNominalIntervals (Bounds Endpoint Argument ContextObligation Obligation
  decomposeArgument decomposeContextArgument childContext effectiveParameter)
open CommonDeclaredNominalInspection (Parameter)
open CommonDeclaredNominalVariance (Variance)
open Core.PresenceGeneration (RowTerm)

inductive OriginalSide where
  | lower
  | upper
  deriving DecidableEq

def OriginalSide.pick (side : OriginalSide) (lower upper : α) : α :=
  match side with
  | .lower => lower
  | .upper => upper

inductive JobFace where
  | left
  | right
  deriving DecidableEq

def JobFace.pick (f : JobFace) (pair : α × α) : α :=
  match f with
  | .left => pair.1
  | .right => pair.2

structure EndpointPort (α : Type) where
  ordinal : Nat
  direction : JobFace
  original : OriginalSide
  payload : α

def comparisonPairs (mode : Variance) (first last : Bounds α) : Option (List (α × α)) :=
  match mode,first,last with
  | .covariant,.point a,.point b => some [(a,b)]
  | .contravariant,.point a,.point b => some [(b,a)]
  | .invariant,a,b => some (a.checks b)
  | .unused,_,_ => some []
  | _,_,_ => none

/-- Projection of one original argument, before learning the other
original argument or comparing them. "none" is not a verdict. For an
open invariant interval both written bounds are retained separately. -/
def endpointPorts (mode : Variance) (side : OriginalSide) (arg : Bounds α) :
    Option (List (EndpointPort α)) :=
  match mode,side,arg with
  | .covariant,.lower,.point a => some [⟨0,.left,.lower,a⟩]
  | .covariant,.upper,.point a => some [⟨0,.right,.upper,a⟩]
  | .contravariant,.lower,.point a => some [⟨0,.right,.lower,a⟩]
  | .contravariant,.upper,.point a => some [⟨0,.left,.upper,a⟩]
  | .invariant,.lower,a => some
      [⟨0,.left,.lower,a.lower⟩,⟨1,.left,.lower,a.lower⟩,
       ⟨0,.right,.upper,a.upper⟩,⟨2,.right,.upper,a.upper⟩]
  | .invariant,.upper,a => some
      [⟨2,.left,.lower,a.lower⟩,⟨3,.left,.lower,a.lower⟩,
       ⟨1,.right,.upper,a.upper⟩,⟨3,.right,.upper,a.upper⟩]
  | .unused,_,_ => some []
  | _,_,_ => none

def EndpointPort.atJob (port : EndpointPort α) (pairs : List (α × α)) : Option α :=
  (pairs[port.ordinal]?).map port.direction.pick

/-- Each represented one-sided observation is the same endpoint at the
same comparative job ordinal and direction if/when the corresponding
paired operation is formed. No comparison truth is needed. -/
theorem endpoint_port_agrees_with_job {mode : Variance} {side : OriginalSide} {first last : Bounds α}
    {entries : List (EndpointPort α)} {pairs : List (α × α)} {read : EndpointPort α}
    (built : comparisonPairs mode first last = some pairs)
    (port : endpointPorts mode side (side.pick first last) = some entries)
    (used : read ∈ entries) :
    read.atJob pairs = some read.payload ∧
      read.payload = read.original.pick (side.pick first last).lower (side.pick first last).upper := by
  cases mode <;> cases side <;> cases first <;> cases last <;> cases built <;> cases port
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used <;>
      first
      | (subst read; exact ⟨rfl,rfl⟩)
      | (rcases used with rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩)

theorem endpoint_port_from_one_original {mode : Variance} {side : OriginalSide} {arg : Bounds α}
    {entries : List (EndpointPort α)} {read : EndpointPort α}
    (found : endpointPorts mode side arg = some entries) (member : read ∈ entries) :
    read.payload = read.original.pick arg.lower arg.upper := by
  cases mode <;> cases side <;> cases arg <;> cases found
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member <;>
      first
      | (subst read; rfl)
      | (rcases member with rfl|rfl|rfl|rfl <;> rfl)

theorem paired_jobs_for_value {parameter : Parameter} {first last : Bounds (Endpoint α)}
    (kind : parameter.kind = .value) :
    decomposeArgument parameter (.inl first) (.inl last) =
      (comparisonPairs parameter.variance first last).map (List.map fun (a,b) => .value a b) := by
  cases parameter with
  | mk k m =>
    cases k
    · cases m <;> cases first <;> cases last <;> rfl
    · cases kind

theorem paired_jobs_for_row {parameter : Parameter} {first last : Bounds (RowTerm α)}
    (kind : parameter.kind = .row) :
    decomposeArgument parameter (.inr first) (.inr last) =
      (comparisonPairs parameter.variance first last).map (List.map fun (a,b) => .row a b) := by
  cases parameter with
  | mk k m =>
    cases k
    · cases kind
    · cases m <;> cases first <;> cases last <;> rfl

theorem value_jobs_in_context (inherited : Bool) (parameter : Parameter)
    {first last : Bounds (Endpoint α)}
    (kind : (effectiveParameter inherited parameter).kind = .value) :
    decomposeContextArgument inherited parameter (.inl first) (.inl last) =
      ((comparisonPairs (effectiveParameter inherited parameter).variance first last).map
        (List.map fun (x,y) => Obligation.value x y)).map
          (List.map fun item => (childContext inherited parameter,item)) := by
  unfold decomposeContextArgument
  rw [paired_jobs_for_value kind]

theorem row_jobs_in_context (inherited : Bool) (parameter : Parameter)
    {first last : Bounds (RowTerm α)}
    (kind : (effectiveParameter inherited parameter).kind = .row) :
    decomposeContextArgument inherited parameter (.inr first) (.inr last) =
      ((comparisonPairs (effectiveParameter inherited parameter).variance first last).map
        (List.map fun (x,y) => Obligation.row x y)).map
          (List.map fun item => (childContext inherited parameter,item)) := by
  unfold decomposeContextArgument
  rw [paired_jobs_for_row kind]

end Yulang.GeneralDeclarativeI65
