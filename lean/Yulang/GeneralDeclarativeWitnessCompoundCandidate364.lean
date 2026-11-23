import Yulang.GeneralDeclarativeWitnessOriginalEndpointProjection364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 82000
set_option maxHeartbeats 105000000
namespace Yulang.GeneralDeclarativeWitnessCompoundCandidate364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root)
open GeneralDeclarativeWitnessOriginalEndpointProjection364 (Projection)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use readUse)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeWitnessProblem349 (declared)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessBareCandidates363 (FitsBare candidate visible)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessNativeValue360 (Code)

def parameter (contra : Bool) : Parameter :=
  ⟨.value,if contra then .contravariant else .covariant⟩

structure Unary (e : Environment) (d : Demand) (row : Declaration) where
  ctor : Nat
  binder : Nat
  variance : Bool
  normalizedHead : row.head.map normalize = [Pattern.app ctor [.var binder]]
  inputArity : d.arguments.length = 1
  sourceCovers : checkDecl e row = true
  request : declared e.source d = true
  owned : Use e ctor 1
  actualMode : names owned.mode 1 = some [parameter variance]
  registry : table[ctor]? = some [parameter variance]

def convert (e : Environment) (d : Demand) (row : Declaration) : Option (Unary e d row) := do
  match shape : row.head.map normalize with
  | [.app key [.var n]] =>
    if covers : d.arguments.length = 1 ∧ checkDecl e row = true ∧ declared e.source d = true then
      let owns ← readUse e key 1
      let variant := names owns.mode 1 = some [parameter true]
      let b := decide variant
      if modes : names owns.mode 1 = some [parameter b] ∧ table[key]? = some [parameter b] then
        pure ⟨key,n,b,shape,covers.1,covers.2.1,covers.2.2,owns,modes.1,modes.2⟩
      else none
    else none
  | _ => none

inductive Disposition {contra : Bool} {x : Ordered contra} {e : Environment} {r : Root x e}
    (p : Projection r) (d : Declaration) : Type where
  | bare : FitsBare e r.occurrence d → Disposition p d
  | matches (source : Unary e r.occurrence d) :
      source.ctor = p.a.head → Disposition p d
  | mismatches (source : Unary e r.occurrence d) :
      source.ctor ≠ p.a.head → source.ctor ≠ p.b.head → Disposition p d

def inspect {contra} {x : Ordered contra} {e : Environment} {r : Root x e}
    (p : Projection r) (d : Declaration) : Option (Disposition p d) := do
  match candidate e r.occurrence d with
  | some bare => pure (.bare bare)
  | none =>
    let shape ← convert e r.occurrence d
    if fits : shape.ctor = p.a.head then pure (.matches shape fits)
    else pure (.mismatches shape fits (fun even => fits (even.trans p.same.symm)))

def Disposition.applies {contra x e r p d} (q : @Disposition contra x e r p d) : Bool :=
  match q with
  | .bare _ | .matches .. => true
  | .mismatches .. => false

inductive Trace {contra : Bool} {x : Ordered contra} {e : Environment} {r : Root x e}
    (p : Projection r) : List Declaration → Type where
  | nil : Trace p []
  | cons : Disposition p k → Trace p rest → Trace p (k::rest)

def scan {contra} {x : Ordered contra} {e : Environment} {r : Root x e} (p : Projection r) :
    (xs : List Declaration) → Option (Trace p xs)
  | [] => some .nil
  | h::t => do
    let first ← inspect p h
    let later ← scan p t
    pure (.cons first later)

def Trace.hits {contra x e r p ds} (t : @Trace contra x e r p ds) : List Declaration :=
  match t with
  | .nil => []
  | @Trace.cons _ _ _ _ _ d _ h tail =>
    if h.applies then d::tail.hits else tail.hits

theorem head_proved_from_both_ends {contra} {x : Ordered contra} {e : Environment} {r : Root x e}
    {p : Projection r} {d} (h : Unary e r.occurrence d) (hit : h.ctor = p.a.head) :
    x.before.native.write.code = .unary h.ctor (.leaf p.a.payload) ∧
    x.after.native.write.code = .unary h.ctor (.leaf p.b.payload) := by
  exact ⟨p.a.exact.trans (congrArg (fun k => Code.unary k (.leaf p.a.payload)) hit.symm),
    p.b.exact.trans (congrArg (fun k => Code.unary k (.leaf p.b.payload)) (p.same.symm.trans hit.symm))⟩

theorem no_laundering_missing_rigid_match {contra} {x : Ordered contra} {e : Environment} {r : Root x e}
    (p : Projection r) (different : Nat) (a : different ≠ p.a.head) :
    x.before.native.write.code ≠ .unary different (.leaf p.a.payload) ∧
    x.after.native.write.code ≠ .unary different (.leaf p.b.payload) := by
  constructor
  · intro common
    exact a (Code.unary.inj (p.a.exact.symm.trans common)).1.symm
  · intro common
    exact a ((Code.unary.inj (p.b.exact.symm.trans common)).1.symm.trans p.same.symm)

end Yulang.GeneralDeclarativeWitnessCompoundCandidate364
