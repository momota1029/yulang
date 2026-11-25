import Yulang.GeneralDeclarativeI65I74ProjectedRetentionTransport423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open GeneralDeclarativeBounds319 (Bound)
open RecordEndpoints422 (Read readAuthoredRecord ProjectedOutput)
open Checker408 (Problem)

inductive BoundStep where
  | interval (ordinal : Nat)
  | ordinary (ordinal : Nat)

/-- A step's actual successor is taken from the original row. The
locator determines where to read, never the type name to regard as
its source or destination. -/
def readBoundStep423 (s : GeneralDeclarativeWhere319.State) (atName : Nat) : BoundStep →
    Option (Σ next : Nat, PLift (Bound s atName next))
  | .interval i =>
    match found : s.intervals[i]? with
    | some (source,next) =>
      if h : source = atName then
        have atEdge : (atName,next) ∈ s.intervals := by
          simpa only [h] using List.mem_of_getElem? found
        some ⟨next,⟨.interval atEdge⟩⟩
      else none
    | none => none
  | .ordinary i =>
    match found : s.ordinary[i]? with
    | some (.tyLe (.var source) (.var next)) =>
      if h : source = atName then
        have atEdge : PresenceNormalForm.Atom.tyLe (.var atName) (.var next) ∈ s.ordinary := by
          simpa only [h] using List.mem_of_getElem? found
        some ⟨next,⟨.constraint atEdge⟩⟩
      else none
    | _ => none

/-- A finite, explicitly located trail, read in order on the original
normal state. The empty trail can prove only reflexivity. -/
def readBoundPath423 (s : GeneralDeclarativeWhere319.State) (fromName toName : Nat) :
    List BoundStep → Option (PLift (Bound s fromName toName))
  | [] => if same : fromName = toName then some ⟨same ▸ .refl fromName⟩ else none
  | step :: tail => do
    let current ← readBoundStep423 s fromName step
    let rest ← readBoundPath423 s current.1 toName tail
    pure ⟨.trans current.2.down rest.down⟩

structure PathWire where
  original : Wire
  lowerToActual : List BoundStep
  actualToUpper : List BoundStep
  resultToLower : List BoundStep
  upperToResult : List BoundStep

/-- This refines *only* the existing retained projection certificate.
Bounds include ordinary variable constraints as well as designated
interval rows. There is no search for a role or treatment of a
missing path as a language rejection. -/
def readRetentionPaths423 {p : Problem} (r : Read p) (w : PathWire) :
    Option (TransportedRetained r) := do
  let reg := w.original
  let raw := p.state.core.current.ordinary
  if sep : reg.lowerName ≠ r.arg.center ∧ reg.upperName ≠ r.arg.center then
    let lower ← readAuthoredRecord p.state reg.lowerName reg.lower
    let upper ← readAuthoredRecord p.state reg.upperName reg.upper
    let below ← readBoundPath423 raw.normal reg.lowerName r.arg.center w.lowerToActual
    let above ← readBoundPath423 raw.normal r.arg.center reg.upperName w.actualToUpper
    if same : lower.label = r.low.label ∧ upper.label = r.low.label then
      match atRow : raw.equations[reg.targetRow]? with
      | some ⟨lhs,.variable observed⟩ =>
        if atTarget : lhs = p.root.demand.outputs[r.outIndex].target then
          let lo ← readBoundPath423 raw.normal observed lower.field w.resultToLower
          let hi ← readBoundPath423 raw.normal upper.field observed w.upperToResult
          have exact : raw.equations[reg.targetRow]? =
              some ⟨p.root.demand.outputs[r.outIndex].target,.variable observed⟩ := by
            simpa only [atTarget] using atRow
          pure ⟨⟨reg.lowerName,reg.upperName,sep.1,sep.2,lower,upper,same.1,same.2,below.down,above.down⟩,
            observed,reg.targetRow,exact,lo.down,hi.down⟩
        else none
      | _ => none
    else none
  else none

theorem checked_path_retains_the_exact_original_B6_value423
    {p : Problem} {r : Read p} {w : PathWire} {retained : TransportedRetained r}
    (_ : readRetentionPaths423 r w = some retained)
    (rhs : ProjectedOutput r) (m : I72.Model) (fit : I72.Fits p.state m) :
    ∃ value : CommonNominalFullCarrier.Ty,
      rhs.actualRightValue m =
        some (p.root.occurrence,r.ordinal,r.outIndex.val,p.root.demand.outputs[r.outIndex].target,value) ∧
      CommonNominalFullCarrier.Equivalent
        (m.assignment p.root.demand.outputs[r.outIndex].target).1 value :=
  original_projected_B6_fixed_target_survives_distinct_logical_names423 rhs retained m fit

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
