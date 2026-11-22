import Yulang.GeneralDeclarativeWitnessReleased350
import Yulang.GeneralDeclarativeWitnessRecordHead350
import Yulang.GeneralDeclarativeWitnessExactProjection349
import Yulang.GeneralDeclarativeTaggedInputs340
import Yulang.GeneralDeclarativeWitnessLiteral349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAuthAllocation351
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeWitnessReleased350 (Checked link usable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support visible)
open GeneralDeclarativeWitnessManifest349 (Link)
open GeneralDeclarativeLowerKnown321 (constructorTag)
open GeneralDeclarativeWitnessRecordHead350 (written renders fields)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeEndpointOverlay336 (Entry footprintKeep receipts spans span_order)
open GeneralDeclarativeEndpointBatch336 (prepare)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeWitnessExactRest349 (Wire)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCommonBridge (Assignment)

variable {before : State} {manifest : Table} {source : Attached before manifest}

def next (out : Checked source arg pat) (keep : List Nat) : State :=
  prepare before (footprintKeep keep out.jobs) out.jobs.length

def used (out : Checked source arg pat) (keep : List Nat) : List (Nat × Capture) :=
  spans before (footprintKeep keep out.jobs) out.jobs

def entries (out : Checked source arg pat) (keep : List Nat) : List Entry :=
  receipts before (footprintKeep keep out.jobs) out.jobs

/-- Decode uses the anchored pre-allocation state and the actual normalized pattern.
It never computes freshness against the later state containing the allocated names. -/
theorem input (out : Checked source arg pat) (keep : List Nat) :
    GeneralDeclarativeTaggedInputs340.Input (support source) c i keep before arg pat
      (next out keep) (used out keep) (entries out keep) :=
  .prior (.record out.pattern out.actual out.computed)

def names (used : List (Nat × Capture)) : List (Nat × Nat × Nat × Nat) :=
  used.map (fun (binder,arg) => (binder,arg.lower,arg.center,arg.upper))

theorem exact_order (out : Checked source arg pat) (keep : List Nat) :
    (used out keep).map Prod.fst = (GeneralDeclarationPatterns.normalize pat).variables :=
  (span_order _ _ _).trans (by
    rw [out.pattern]; exact (GeneralDeclarativeEndpointProgram336.list_sound out.actual out.computed).1)

/-- This check compares the literal named slots, in sequence (including duplicate
binder positions), before deriving the actual model of the projection sidecar. -/
def check (out : Checked source arg pat) (keep : List Nat) (current : State)
    (reported : List (Nat × Nat × Nat × Nat)) (exact : List Wire) : Bool :=
  (GeneralDeclarativeWitnessLiteral349.preserves (next out keep) current &&
   decide (reported = names (used out keep))) &&
    GeneralDeclarativeWitnessExactProjection349.checkedList current (entries out keep) exact

theorem sound {out : Checked source arg pat} {keep current reported exact}
    (ok : check out keep current reported exact = true) :
    Extends (next out keep) current ∧
      reported = names (used out keep) ∧
      ∀ m : Assignment, Models current m → ModelsExact current (entries out keep) m := by
  have ⟨part,projections⟩ := splitAnd ok
  have ⟨growth,order⟩ := splitAnd part
  exact ⟨(GeneralDeclarativeWitnessLiteral349.preserves_iff _ _).mp growth,
    of_decide_eq_true order,fun m fit => GeneralDeclarativeWitnessExactProjection349.fixed_models projections m fit⟩

theorem observed {out : Checked source arg pat} {keep current reported exact}
    {c : GeneralDeclarationPatterns.Constructors} {i : GeneralNominalInspection.Interpretation}
    (ok : check out keep current reported exact = true) (m : Assignment) (fit : Models current m) :
    GeneralDeclarativeExactDictionary337.Observed c i m arg pat := by
  have ⟨later,_,holds⟩ := sound ok
  have assembled : GeneralDeclarativeTaggedInputs340.Inputs (support source) c i keep
      before [arg] [pat] (next out keep) (used out keep ++ []) (entries out keep ++ []) :=
    .cons (input out keep) .nil
  have reads : ∀ e ∈ entries out keep ++ [], GeneralDeclarativeExactOverlay337.Holds m e :=
    fun e p => (holds m fit).2 e (by simpa using p)
  cases GeneralDeclarativeTaggedInputs340.observed assembled
      (GeneralDeclarativeClauseBatch327.reflexive before) later m fit reads with
  | cons first _ => exact first

/-- Actual backed bounds and spines establish the tag-free record Head.
The availability proof retains its producer identity, including release. -/
theorem head (out : Checked source arg pat) (nonempty : out.fields ≠ [])
    (c : GeneralDeclarationPatterns.Constructors) (i : GeneralNominalInspection.Interpretation) :
    GeneralDeclarativeTaggedElection340.Head (support source) c i arg pat := by
  have distinctKeys : out.fields.map Prod.fst ≠ [] := fun empty => nonempty (List.map_eq_nil_iff.mp empty)
  obtain ⟨lo,knownLo⟩ := fields (mode := .lower) (s := restriction (support source))
    (GeneralDeclarativeEndpointRecord336.labels out.actual).1
  obtain ⟨hi,knownHi⟩ := fields (mode := .upper) (s := restriction (support source))
    (GeneralDeclarativeEndpointRecord336.labels out.actual).2
  apply GeneralDeclarativeTaggedElection340.Head.old
  refine ⟨out.actual.valid,withTail (written out.fields) (.variable out.tail),
    lo ++ [⟨out.tail,.lower,tailExpr out.low.fields (out.fields.map Prod.fst) out.low.ending⟩],
    hi ++ [⟨out.tail,.upper,tailExpr out.high.fields (out.fields.map Prod.fst) out.high.ending⟩],?_,?_,?_⟩
  · rw [out.pattern]
    exact renders c i out.fields out.tail
  · exact .record (.name out.actual.lo) out.actual.distinct distinctKeys
      out.actual.displayedLow knownLo .binder .capture
  · exact .record (.name out.actual.hi) out.actual.distinct distinctKeys
      out.actual.displayedHigh knownHi .binder .capture

structure Seen {s : State} {t : Table} (a : Attached s t) (n : Nat) where
  tag : GeneralDeclarativeLowerKnown321.Tag
  result : GeneralDeclarativeLowerKnown321.Knows (restriction (support a)) n tag

def know {s : State} {t : Table} (a : Attached s t) (n idx : Nat)
    (aliased : Link) : Option (Seen a n) := do
  match seen : (visible t)[idx]? with
  | none => none
  | some e =>
    let proof ← link a n e.left aliased
    match tag : constructorTag e.right with
    | none => none
    | some name => pure ⟨name,e,usable a seen,proof.property,tag⟩

end Yulang.GeneralDeclarativeWitnessAuthAllocation351
