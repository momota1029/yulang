import Yulang.GeneralDeclarativeWitnessVariancePositions357
import Yulang.GeneralSourceMetadataBareBundle291
import Yulang.GeneralNominalCenteredHeadWFSource

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessConstructorModes357
open GeneralDeclarativeWitnessSparseVariance357 (Source Made lookup)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (constructors primitives invariants)
open GeneralCandidateInspection (Primitive)
open GeneralDeclarationPatterns (Constructor ParameterKind)
open CommonDeclaredNominalInspection (Kind Parameter)

structure Environment where
  nodes : Nat
  types : Nat
  rows : Nat
  bodies : Source nodes types rows
  graph : Made bodies
  source : SourceBundle

inductive Mode where
  | primitive (operation : Primitive)
  | invariant
  | declared (parameters : List Parameter)

def targetKind : Kind → ParameterKind
  | .value => .type
  | .row => .row

def Layout (ctor : Constructor) : Mode → Prop
  | .primitive p => ctor.parameters = p.parameters
  | .invariant => ctor.parameters = List.replicate ctor.parameters.length .type
  | .declared ps => ctor.parameters = ps.map (targetKind ∘ Parameter.kind)

instance (ctor : Constructor) (m : Mode) : Decidable (Layout ctor m) := by
  cases m <;> unfold Layout <;> infer_instance

inductive SourceMode (e : Environment) (name : Nat) : Mode → Prop
  | primitive {p : Primitive} : primitives e.source.snapshot name = some p →
      lookup e.graph name = none → SourceMode e name (.primitive p)
  | invariant : invariants e.source.snapshot name = true →
      lookup e.graph name = none → SourceMode e name .invariant
  | declared {p : List Parameter} : lookup e.graph name = some p →
      primitives e.source.snapshot name = none → invariants e.source.snapshot name = false →
      SourceMode e name (.declared p)

structure Use (e : Environment) (name arity : Nat) where
  declared : Constructor
  current : Constructor
  actual : constructors e.source.declared name = some declared
  snapshot : constructors e.source.snapshot name = some current
  declaredName : declared.name = name
  currentName : current.name = name
  sameLayout : current.parameters = declared.parameters
  exactArity : declared.parameters.length = arity
  mode : Mode
  sourced : SourceMode e name mode
  kinded : Layout declared mode
  noDefault : e.source.declared.fallback = .absent ∧ e.source.snapshot.fallback = .absent

def readMode (e : Environment) (name : Nat) : Option {m : Mode // SourceMode e name m} :=
  match var : lookup e.graph name with
  | some ps =>
    match prim : primitives e.source.snapshot name, inv : invariants e.source.snapshot name with
    | none,false => some ⟨.declared ps,.declared var prim inv⟩
    | _,_ => none
  | none =>
    match prim : primitives e.source.snapshot name with
    | some p => some ⟨.primitive p,.primitive prim var⟩
    | none =>
      if inv : invariants e.source.snapshot name = true then
        some ⟨.invariant,.invariant inv var⟩
      else none

def readUse (e : Environment) (name arity : Nat) : Option (Use e name arity) :=
  if noDefault : e.source.declared.fallback = .absent ∧ e.source.snapshot.fallback = .absent then
    match written : constructors e.source.declared name, live : constructors e.source.snapshot name with
    | some declared,some current => do
      let mode ← readMode e name
      if exact : declared.name = name ∧ current.name = name ∧
          current.parameters = declared.parameters ∧ declared.parameters.length = arity ∧
          Layout declared mode.val then
        some ⟨declared,current,written,live,exact.1,exact.2.1,exact.2.2.1,exact.2.2.2.1,
          mode.val,mode.property,exact.2.2.2.2,noDefault⟩
      else none
    | _,_ => none
  else none

theorem check_has_no_fallback {e : Environment} {name arity} (use : Use e name arity) :
    (registry e.source).constructors name = some use.declared ∧
      use.declared.parameters.length = arity ∧ name ∈ e.source.declared.rows.map GeneralSourceMetadataRows291.Row.key := by
  refine ⟨use.actual,use.exactArity,?_⟩
  by_cases present : name ∈ e.source.declared.rows.map GeneralSourceMetadataRows291.Row.key
  · exact present
  · have none_ := GeneralSourceMetadataRows291.outside_constructor e.source.declared name present
    rw [use.noDefault.1,use.actual] at none_
    cases none_

theorem declared_mode_from_bodies {e : Environment} {name params}
    (use : SourceMode e name (.declared params)) :
    ∃ h ∈ e.bodies.headers, h.name = name ∧
      CommonRoleOutermostResolver.All₂ (GeneralDeclarativeWitnessVariancePositions357.sourced e.graph.program)
        h.written params := by
  cases use with
  | declared exact _ _ =>
    exact GeneralDeclarativeWitnessVariancePositions357.authored_modes_exact e.graph exact

end Yulang.GeneralDeclarativeWitnessConstructorModes357
