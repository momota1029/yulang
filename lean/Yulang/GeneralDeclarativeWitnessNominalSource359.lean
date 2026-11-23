import Yulang.GeneralDeclarativeWitnessFullIntervals357
import Yulang.GeneralDeclarativeWitnessModeCoverage357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNominalSource359
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessConstructorModes357 (Environment readUse Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names Compiled)
open CommonRecursiveNominalIntervals (Endpoint Argument childContext effectiveParameter)
open CommonDeclaredNominalInspection (Registry Parameter)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)

inductive Location where
  | head (implId implOrdinal argumentOrdinal : Nat)
  | requirement (implId implOrdinal clauseId clauseOrdinal argumentOrdinal : Nat)

/-- Read the literal source first: position and stable id are both checked,
and only then apply the existing normalizer. -/
def written (e : Environment) : Location → Option Pattern
  | .head id decl item => do
    let d ← e.source.declarations[decl]?
    if d.id = id then d.head[item]? else none
  | .requirement id decl clauseId clause item => do
    let d ← e.source.declarations[decl]?
    if d.id = id then
      let c ← d.requirements[clause]?
      if c.id = clauseId then c.arguments[item]? else none
    else none

inductive Route where
  | bind (binder : Nat)
  | nullary (ctor : Nat)
  | unary (ctor : Nat) (argument : Route)

def Route.pattern : Route → Pattern
  | .bind n => .var n
  | .nullary c => .app c []
  | .unary c a => .app c [a.pattern]

def AtSource (e : Environment) (site : Location) (r : Route) : Prop :=
  (written e site).map normalize = some r.pattern

abbrev SlotRead := Nat → Option Capture

def argumentSlot (outer : Bool) (mode : Parameter) (c : Capture) : Argument Nat :=
  if (effectiveParameter outer mode).variance = .invariant then
    .inl (.interval (.ordinary (.var c.lower)) (.ordinary (.var c.upper)))
  else .inl (.point (.ordinary (.var c.center)))

/-- Lower authored unary value applications without a model oracle.
A variable in inherited invariant context retains both sourced bounds
and is not replaced by its actual point. For unused arguments, the
compiler still checks the nested syntax and its actual declaration. -/
def lower (e : Environment) (table : Registry) (slots : SlotRead) (context : Bool) :
    Route → Option (Endpoint Nat)
  | .bind binder => (slots binder).map fun c => .ordinary (.var c.center)
  | .nullary ctor => do
    let use ← readUse e ctor 0
    if names use.mode 0 = some [] ∧ table[ctor]? = some [] then some (.nominal ctor []) else none
  | .unary ctor arg => do
    let use ← readUse e ctor 1
    match names use.mode 1 with
    | some [p] =>
      if p.kind = .value ∧ table[ctor]? = some [p] then
        match arg with
        | .bind binder => do
          let c ← slots binder
          pure (.nominal ctor [argumentSlot context p c])
        | other => do
          let child ← lower e table slots (childContext context p) other
          pure (.nominal ctor [.inl (.point child)])
      else none
    | _ => none

structure Built (e : Environment) (table : Registry) (slots : SlotRead)
    (context : Bool) (site : Location) (r : Route) where
  source : AtSource e site r
  endpoint : Endpoint Nat
  lowered : lower e table slots context r = some endpoint

def build (e : Environment) (table : Registry) (slots : SlotRead)
    (context : Bool) (site : Location) (r : Route) : Option (Built e table slots context site r) :=
  if valid : (written e site).map normalize = some r.pattern then
    match result : lower e table slots context r with
    | none => none
    | some endpoint => some ⟨valid,endpoint,result⟩
  else none

theorem never_without_source {e table slots context site route}
    (seen : (build e table slots context site route).isSome = true) : AtSource e site route := by
  unfold build at seen
  split at seen
  · assumption
  · contradiction

structure Compared (e : Environment) (table : Registry) (slots : SlotRead)
    (context : Bool) (left right : Location) (a b : Route) where
  first : Built e table slots context left a
  last : Built e table slots context right b
  run : Compiled e table context first.endpoint last.endpoint

def compare (e : Environment) (table : Registry) (slots : SlotRead)
    (context : Bool) (left right : Location) (a b : Route) :
    Option (Compared e table slots context left right a b) := do
  let first ← build e table slots context left a
  let last ← build e table slots context right b
  let run ← GeneralDeclarativeWitnessSparseIntervals357.compile e table context first.endpoint last.endpoint
  pure ⟨first,last,run⟩

theorem approved_source_comparison {e table slots context left right a b}
    (proof : Compared e table slots context left right a b)
    {s : State} (retained : ∀ atom ∈ proof.run.rows,atom ∈ s.normal.ordinary)
    (m : Assignment) (fit : Models s m) :
    AtSource e left a ∧ AtSource e right b ∧
    CommonRecursiveNominalIntervals.ContextWellFormed table context proof.first.endpoint ∧
    CommonRecursiveNominalIntervals.ContextWellFormed table context proof.last.endpoint ∧
    GeneralDeclarativeWitnessFullIntervals357.ContextDerives table m context proof.first.endpoint proof.last.endpoint :=
  ⟨proof.first.source,proof.last.source,GeneralDeclarativeWitnessFullIntervals357.in_current_full_model
    proof.run retained m fit⟩

end Yulang.GeneralDeclarativeWitnessNominalSource359
