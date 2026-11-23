import Yulang.GeneralDeclarativeWitnessScopedBindings359
import Yulang.GeneralDictionaryAssociatedProvenance

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessAssociatedDescriptor359
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey Frame slots findFrame)
open GeneralDeclarativeWitnessNominalSource359 (Route lower)
open GeneralDeclarativeWitnessNominalRelation359 (Reads lower_sound)
open GeneralDeclarativeWitnessNominalExact359 (read_compile)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeDemand320 (Demand)
open GeneralSourceState (Output)
open GeneralDeclarations (Declaration Equation)
open GeneralSourceMetadataBundle291 (registry)
open GeneralDeclarationPatterns (normalize)
open GeneralDictionaryAssociatedProvenance (lookup Supplies lookup_exact)
open CommonDeclaredNominalInspection (Registry)
open CommonRecursiveNominalIntervals (Endpoint)

def binders : Route → List Nat
  | .bind n => [n]
  | .nullary _ => []
  | .unary _ t => binders t

def licensed (e : Environment) (fs : List Frame) (key : FrameKey)
    (d : Demand) (decl : Declaration) (out : Output) (route : Route) : Prop :=
    (findFrame fs key).isSome = true ∧
      (((registry e.source).roles d.role).assoc out.name).isSome = true ∧
      (binders route).all (fun b => decide (b ∈ decl.inputNames)) = true

instance (e : Environment) (fs : List Frame) (key : FrameKey) (d : Demand)
    (decl : Declaration) (out : Output) (route : Route) :
    Decidable (licensed e fs key d decl out route) := by unfold licensed; infer_instance

structure Wire where
  ordinal : Nat
  sourceEquation : Nat
  target : Nat
  route : Route

/-- A checked *description*, not a value-carrying ordinary nominal write.
The fixed physical target and associated ordinal are part of the source
receipt. The output is not installed in the current state by this checker. -/
structure Described (e : Environment) (table : Registry) (frames : List Frame)
    (key : FrameKey) (d : Demand) (wire : Wire) where
  declaration : Declaration
  selectedSource : e.source.declarations[key.sourceOrdinal]? = some declaration
  identity : declaration.id = key.declaration ∧ declaration.role = d.role
  uniqueNames : (declaration.associated.map Equation.name).Nodup
  requested : Output
  indexed : d.outputs[wire.ordinal]? = some requested
  fixed : requested.target = wire.target
  authority : licensed e frames key d declaration requested wire.route
  authored : Equation
  actualLookup : lookup (registry e.source).roles declaration requested.name = some (.explicit authored)
  equationId : authored.id = wire.sourceEquation
  written : normalize authored.rhs = wire.route.pattern
  endpoint : Endpoint Nat
  compiled : lower e table (slots frames key) false wire.route = some endpoint

def describe (e : Environment) (table : Registry) (frames : List Frame)
    (key : FrameKey) (d : Demand) (wire : Wire) : Option (Described e table frames key d wire) :=
  match located : e.source.declarations[key.sourceOrdinal]? with
  | none => none
  | some declaration =>
    if identity : declaration.id = key.declaration ∧ declaration.role = d.role then
      if unique : (declaration.associated.map Equation.name).Nodup then
        match indexed : d.outputs[wire.ordinal]? with
        | none => none
        | some out =>
          if fixed : out.target = wire.target then
            if grant : licensed e frames key d declaration out wire.route then
              match found : lookup (registry e.source).roles declaration out.name with
              | some (.explicit authored) =>
                if id : authored.id = wire.sourceEquation then
                  if raw : normalize authored.rhs = wire.route.pattern then
                    match compiled : lower e table (slots frames key) false wire.route with
                    | some endpoint => some ⟨declaration,located,identity,unique,out,indexed,fixed,grant,authored,
                        found,id,raw,endpoint,compiled⟩
                    | none => none
                  else none
                else none
              | _ => none
            else none
          else none
      else none
    else none

theorem exact_authored_address {e table fs key d wire} (output : Described e table fs key d wire) :
    e.source.declarations[key.sourceOrdinal]? = some output.declaration ∧
    output.declaration.id = key.declaration ∧ output.declaration.role = d.role ∧
    d.outputs[wire.ordinal]? = some output.requested ∧ output.requested.target = wire.target ∧
    Supplies (registry e.source).roles output.declaration output.requested.name (.explicit output.authored) ∧
    output.authored.id = wire.sourceEquation ∧ normalize output.authored.rhs = wire.route.pattern ∧
    Reads e table (slots fs key) false wire.route output.endpoint :=
  ⟨output.selectedSource,output.identity.1,output.identity.2,output.indexed,output.fixed,
    (lookup_exact _ _ output.uniqueNames _ _).mp output.actualLookup,
    output.equationId,output.written,lower_sound output.compiled⟩

theorem fixed_target_is_never_a_model_choice {e table fs key d wire} (output : Described e table fs key d wire) :
    ∃ out, d.outputs[wire.ordinal]? = some out ∧ out.target = wire.target :=
  ⟨output.requested,output.indexed,output.fixed⟩

theorem authorized_inputs_only {e table fs key d wire} (output : Described e table fs key d wire) :
    (findFrame fs key).isSome = true ∧
    (∃ body, ((registry e.source).roles d.role).assoc output.requested.name = some body) ∧
    ∀ b ∈ binders wire.route,b ∈ output.declaration.inputNames := by
  have declared := output.authority.2.1
  refine ⟨output.authority.1,?_ ,?_⟩
  · cases lookup : ((registry e.source).roles d.role).assoc output.requested.name with
    | none => rw [lookup] at declared; cases declared
    | some body => exact ⟨body,rfl⟩
  · intro b membership
    exact of_decide_eq_true (List.all_eq_true.mp output.authority.2.2 b membership)

end Yulang.GeneralDeclarativeWitnessAssociatedDescriptor359
