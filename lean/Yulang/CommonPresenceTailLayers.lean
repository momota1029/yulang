import Yulang.CommonPresenceTailElimination
import Yulang.CommonLayerCongruence

/-!
# Symbolic payload layers for the common same-depth solver

Same-depth references and guarded payload references have different syntax.
Atoms are ordinary common layers with arbitrary payload indices; record heads
and default fallbacks also retain those indices. In particular a layer atom
may contain an arrow whose negative argument refers to the same unknown
graph as its result. The solver never substitutes or orders those payloads.

The algorithm is the existing four-mode solver's finite intersection/union
iteration, executed on layer syntax. Quoting any payload assignment commutes
literally with the existing concrete solver. Finite-depth interpretation also
commutes with the iteration, including the depth-zero default approximation.
No solver correctness law is a field of this syntax or a premise of the
commutation theorems.
-/

namespace Yulang.CommonPresenceTailLayers

open CommonSyntax (Layer State)
open PresenceTailElimination (Mask)
open PositiveEquationElimination (iterate)
open CommonPresenceTailElimination (observationCoordinates)

variable {slots labels : Nat} {Index Target : Type}

inductive Body (slots labels : Nat) (Index : Type) where
  | atom : Layer Common.Row Index → Body slots labels Index
  | ref : Fin slots → Body slots labels Index
  | union : Body slots labels Index → Body slots labels Index → Body slots labels Index
  | inter : Body slots labels Index → Body slots labels Index → Body slots labels Index
  | mask : Mask labels → Body slots labels Index → Body slots labels Index
  | record : Nat → Index → Body slots labels Index → Body slots labels Index
  | recordDefault : Nat → Body slots labels Index → Index → Body slots labels Index

def quoteLayer (assignment : Index → Common.Ty) (layer : Layer Common.Row Index) : Common.Ty :=
  layer.map (fun index => State.node (assignment index))

@[simp] theorem quoteLayer_map (rename : Index → Target) (assignment : Target → Common.Ty)
    (layer : Layer Common.Row Index) :
    quoteLayer assignment (layer.map rename) = quoteLayer (assignment ∘ rename) layer := by
  simp only [quoteLayer, Layer.map_comp]
  rfl

namespace Body

def map (rename : Index → Target) : Body slots labels Index → Body slots labels Target
  | .atom layer => .atom (layer.map rename)
  | .ref index => .ref index
  | .union first last => .union (map rename first) (map rename last)
  | .inter first last => .inter (map rename first) (map rename last)
  | .mask hidden body => .mask hidden (map rename body)
  | .record label payload tail => .record label (rename payload) (map rename tail)
  | .recordDefault label source fallback => .recordDefault label (map rename source) (rename fallback)

def evalLayers (tails : Fin slots → Layer Common.Row Index) :
    Body slots labels Index → Layer Common.Row Index
  | .atom layer => layer
  | .ref index => tails index
  | .union first last => .union (evalLayers tails first) (evalLayers tails last)
  | .inter first last => .inter (evalLayers tails first) (evalLayers tails last)
  | .mask hidden body => .mask hidden.names (evalLayers tails body)
  | .record label payload tail => .record label payload (evalLayers tails tail)
  | .recordDefault label source fallback => .recordDefault label (evalLayers tails source) fallback

def quote (assignment : Index → Common.Ty) :
    Body slots labels Index → CommonPresenceTailElimination.Body slots labels
  | .atom layer => .atom (quoteLayer assignment layer)
  | .ref index => .ref index
  | .union first last => .union (quote assignment first) (quote assignment last)
  | .inter first last => .inter (quote assignment first) (quote assignment last)
  | .mask hidden body => .mask hidden (quote assignment body)
  | .record label payload tail => .record label (assignment payload) (quote assignment tail)
  | .recordDefault label source fallback => .recordDefault label (quote assignment source) (assignment fallback)

@[simp] theorem quote_map (body : Body slots labels Index) (rename : Index → Target)
    (assignment : Target → Common.Ty) :
    (body.map rename).quote assignment = body.quote (assignment ∘ rename) := by
  induction body <;> simp_all [map, quote, Function.comp_def]

theorem evalLayers_map (body : Body slots labels Index) (rename : Index → Target)
    (tails : Fin slots → Layer Common.Row Index) :
    (body.map rename).evalLayers (fun index => (tails index).map rename) =
      (body.evalLayers tails).map rename := by
  induction body <;> simp_all [map, evalLayers, Layer.map]

theorem evalLayers_quote (body : Body slots labels Index) (assignment : Index → Common.Ty)
    (tails : Fin slots → Layer Common.Row Index) :
    quoteLayer assignment (body.evalLayers tails) =
      (body.quote assignment).eval (fun index => quoteLayer assignment (tails index)) := by
  induction body <;> simp_all [evalLayers, quote, quoteLayer, Layer.map,
    CommonPresenceTailElimination.Body.eval, Common.mask, Common.record, Common.recordDefault]

/-- Independent finite interpretation: payloads are already observed one
guard below, while same-depth references use the supplied tail family. -/
def evalAt (depth : Nat) (payloads : Index → CommonFinite.Ty Common.Row)
    (tails : Fin slots → CommonFinite.Ty Common.Row) :
    Body slots labels Index → CommonFinite.Ty Common.Row
  | .atom layer => layer.evalAt depth payloads
  | .ref index => tails index
  | .union first last => .union (evalAt depth payloads tails first) (evalAt depth payloads tails last)
  | .inter first last => .inter (evalAt depth payloads tails first) (evalAt depth payloads tails last)
  | .mask hidden body => .mask hidden.names (evalAt depth payloads tails body)
  | .record label payload tail => .record label (payloads payload) (evalAt depth payloads tails tail)
  | .recordDefault label source fallback =>
      match depth with
      | 0 => .record label .bottom (evalAt 0 payloads tails source)
      | previous + 1 => .recordDefault label (evalAt (previous + 1) payloads tails source) (payloads fallback)

theorem evalLayers_evalAt (body : Body slots labels Index) (depth : Nat)
    (payloads : Index → CommonFinite.Ty Common.Row) (tails : Fin slots → Layer Common.Row Index) :
    (body.evalLayers tails).evalAt depth payloads =
      body.evalAt depth payloads (fun index => (tails index).evalAt depth payloads) := by
  induction body <;> simp_all [evalLayers, evalAt, Layer.evalAt]
  case recordDefault => cases depth <;> simp_all

end Body

abbrev Graph (slots labels : Nat) (Index : Type) := Fin slots → Body slots labels Index

def mapGraph (rename : Index → Target) (graph : Graph slots labels Index) : Graph slots labels Target :=
  fun index => (graph index).map rename

def mapFamily (rename : Index → Target) (family : Fin slots → Layer Common.Row Index) :
    Fin slots → Layer Common.Row Target := fun index => (family index).map rename

def quoteGraph (assignment : Index → Common.Ty) (graph : Graph slots labels Index) :
    CommonPresenceTailElimination.Graph slots labels := fun index => (graph index).quote assignment

def quoteFamily (assignment : Index → Common.Ty) (family : Fin slots → Layer Common.Row Index) :
    Fin slots → Common.Ty := fun index => quoteLayer assignment (family index)

def step (graph : Graph slots labels Index) (family : Fin slots → Layer Common.Row Index) :
    Fin slots → Layer Common.Row Index := fun index => (graph index).evalLayers family

def ascend (graph : Graph slots labels Index) (family : Fin slots → Layer Common.Row Index) :
    Fin slots → Layer Common.Row Index := fun index => .inter (family index) (step graph family index)

def descend (graph : Graph slots labels Index) (family : Fin slots → Layer Common.Row Index) :
    Fin slots → Layer Common.Row Index := fun index => .union (family index) (step graph family index)

def solveLayers (graph : Graph slots labels Index) (parameters : Fin slots → Layer Common.Row Index) :
    Fin slots → Layer Common.Row Index :=
  iterate (descend graph) (observationCoordinates slots labels).length
    (iterate (ascend graph) (observationCoordinates slots labels).length parameters)

theorem map_step (graph : Graph slots labels Index) (rename : Index → Target)
    (family : Fin slots → Layer Common.Row Index) :
    mapFamily rename (step graph family) = step (mapGraph rename graph) (mapFamily rename family) := by
  funext index
  exact ((graph index).evalLayers_map rename family).symm

theorem map_ascend (graph : Graph slots labels Index) (rename : Index → Target)
    (family : Fin slots → Layer Common.Row Index) :
    mapFamily rename (ascend graph family) = ascend (mapGraph rename graph) (mapFamily rename family) := by
  funext index
  exact congrArg (Layer.inter ((family index).map rename)) (congrFun (map_step graph rename family) index)

theorem map_descend (graph : Graph slots labels Index) (rename : Index → Target)
    (family : Fin slots → Layer Common.Row Index) :
    mapFamily rename (descend graph family) = descend (mapGraph rename graph) (mapFamily rename family) := by
  funext index
  exact congrArg (Layer.union ((family index).map rename)) (congrFun (map_step graph rename family) index)

theorem map_solveLayers (graph : Graph slots labels Index) (parameters : Fin slots → Layer Common.Row Index)
    (rename : Index → Target) :
    mapFamily rename (solveLayers graph parameters) =
      solveLayers (mapGraph rename graph) (mapFamily rename parameters) := by
  unfold solveLayers
  rw [PositiveEquationElimination.iterate_commute (descend graph) (descend (mapGraph rename graph))
    (mapFamily rename) (map_descend graph rename)]
  rw [PositiveEquationElimination.iterate_commute (ascend graph) (ascend (mapGraph rename graph))
    (mapFamily rename) (map_ascend graph rename)]

theorem solveLayers_map (graph : Graph slots labels Index) (parameters : Fin slots → Layer Common.Row Index)
    (rename : Index → Target) (index : Fin slots) :
    (solveLayers graph parameters index).map rename =
      solveLayers (mapGraph rename graph) (mapFamily rename parameters) index :=
  congrFun (map_solveLayers graph parameters rename) index

theorem quote_step (graph : Graph slots labels Index) (assignment : Index → Common.Ty)
    (family : Fin slots → Layer Common.Row Index) :
    quoteFamily assignment (step graph family) =
      CommonPresenceTailElimination.step (quoteGraph assignment graph) (quoteFamily assignment family) := by
  funext index
  exact (graph index).evalLayers_quote assignment family

theorem quote_ascend (graph : Graph slots labels Index) (assignment : Index → Common.Ty)
    (family : Fin slots → Layer Common.Row Index) :
    quoteFamily assignment (ascend graph family) =
      CommonPresenceTailElimination.ascend (quoteGraph assignment graph) (quoteFamily assignment family) := by
  funext index
  exact congrArg (Layer.inter (quoteLayer assignment (family index)))
    (congrFun (quote_step graph assignment family) index)

theorem quote_descend (graph : Graph slots labels Index) (assignment : Index → Common.Ty)
    (family : Fin slots → Layer Common.Row Index) :
    quoteFamily assignment (descend graph family) =
      CommonPresenceTailElimination.descend (quoteGraph assignment graph) (quoteFamily assignment family) := by
  funext index
  exact congrArg (Layer.union (quoteLayer assignment (family index)))
    (congrFun (quote_step graph assignment family) index)

theorem quote_solveLayers (graph : Graph slots labels Index) (parameters : Fin slots → Layer Common.Row Index)
    (assignment : Index → Common.Ty) :
    quoteFamily assignment (solveLayers graph parameters) =
      CommonPresenceTailElimination.solve (quoteGraph assignment graph) (quoteFamily assignment parameters) := by
  unfold solveLayers CommonPresenceTailElimination.solve
  rw [PositiveEquationElimination.iterate_commute (descend graph)
    (CommonPresenceTailElimination.descend (quoteGraph assignment graph))
    (quoteFamily assignment) (quote_descend graph assignment)]
  rw [PositiveEquationElimination.iterate_commute (ascend graph)
    (CommonPresenceTailElimination.ascend (quoteGraph assignment graph))
    (quoteFamily assignment) (quote_ascend graph assignment)]

/-- Literal commutation with the already proved concrete four-mode solver,
for every payload assignment and every independent layer parameter family. -/
theorem solveLayers_quote (graph : Graph slots labels Index) (parameters : Fin slots → Layer Common.Row Index)
    (assignment : Index → Common.Ty) (index : Fin slots) :
    quoteLayer assignment (solveLayers graph parameters index) =
      CommonPresenceTailElimination.solve (quoteGraph assignment graph) (quoteFamily assignment parameters) index :=
  congrFun (quote_solveLayers graph parameters assignment) index

def evalFamilyAt (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (family : Fin slots → Layer Common.Row Index) : Fin slots → CommonFinite.Ty Common.Row :=
  fun index => (family index).evalAt depth assignment

def stepAt (graph : Graph slots labels Index) (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (family : Fin slots → CommonFinite.Ty Common.Row) : Fin slots → CommonFinite.Ty Common.Row :=
  fun index => (graph index).evalAt depth assignment family

def ascendAt (graph : Graph slots labels Index) (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (family : Fin slots → CommonFinite.Ty Common.Row) : Fin slots → CommonFinite.Ty Common.Row :=
  fun index => .inter (family index) (stepAt graph depth assignment family index)

def descendAt (graph : Graph slots labels Index) (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (family : Fin slots → CommonFinite.Ty Common.Row) : Fin slots → CommonFinite.Ty Common.Row :=
  fun index => .union (family index) (stepAt graph depth assignment family index)

def solveAt (graph : Graph slots labels Index) (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (parameters : Fin slots → CommonFinite.Ty Common.Row) : Fin slots → CommonFinite.Ty Common.Row :=
  iterate (descendAt graph depth assignment) (observationCoordinates slots labels).length
    (iterate (ascendAt graph depth assignment) (observationCoordinates slots labels).length parameters)

theorem eval_step (graph : Graph slots labels Index) (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (family : Fin slots → Layer Common.Row Index) :
    evalFamilyAt depth assignment (step graph family) = stepAt graph depth assignment (evalFamilyAt depth assignment family) := by
  funext index
  exact (graph index).evalLayers_evalAt depth assignment family

theorem eval_ascend (graph : Graph slots labels Index) (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (family : Fin slots → Layer Common.Row Index) :
    evalFamilyAt depth assignment (ascend graph family) = ascendAt graph depth assignment (evalFamilyAt depth assignment family) := by
  funext index
  exact congrArg (CommonFinite.Ty.inter ((family index).evalAt depth assignment))
    (congrFun (eval_step graph depth assignment family) index)

theorem eval_descend (graph : Graph slots labels Index) (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row)
    (family : Fin slots → Layer Common.Row Index) :
    evalFamilyAt depth assignment (descend graph family) = descendAt graph depth assignment (evalFamilyAt depth assignment family) := by
  funext index
  exact congrArg (CommonFinite.Ty.union ((family index).evalAt depth assignment))
    (congrFun (eval_step graph depth assignment family) index)

theorem eval_solveLayers (graph : Graph slots labels Index) (parameters : Fin slots → Layer Common.Row Index)
    (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row) :
    evalFamilyAt depth assignment (solveLayers graph parameters) =
      solveAt graph depth assignment (evalFamilyAt depth assignment parameters) := by
  unfold solveLayers solveAt
  rw [PositiveEquationElimination.iterate_commute (descend graph) (descendAt graph depth assignment)
    (evalFamilyAt depth assignment) (eval_descend graph depth assignment)]
  rw [PositiveEquationElimination.iterate_commute (ascend graph) (ascendAt graph depth assignment)
    (evalFamilyAt depth assignment) (eval_ascend graph depth assignment)]

theorem solveLayers_evalAt (graph : Graph slots labels Index) (parameters : Fin slots → Layer Common.Row Index)
    (depth : Nat) (assignment : Index → CommonFinite.Ty Common.Row) (index : Fin slots) :
    (solveLayers graph parameters index).evalAt depth assignment =
      solveAt graph depth assignment (evalFamilyAt depth assignment parameters) index :=
  congrFun (eval_solveLayers graph parameters depth assignment) index

theorem quoteLayer_observe (depth : Nat) (assignment : Index → Common.Ty) (layer : Layer Common.Row Index) :
    Common.observeTy depth (quoteLayer assignment layer) =
      layer.evalAt depth (fun index => CommonSyntax.observe (CommonSyntax.graph Common.Row) depth (.node (assignment index))) := by
  exact Layer.evalAt_map depth _ _ layer

theorem quoteLayer_observe_zero (assignment : Index → Common.Ty) (layer : Layer Common.Row Index) :
    Common.observeTy 0 (quoteLayer assignment layer) = layer.evalAt 0 (fun _ => .bottom) :=
  quoteLayer_observe 0 assignment layer

theorem quoteLayer_observe_succ (depth : Nat) (assignment : Index → Common.Ty) (layer : Layer Common.Row Index) :
    Common.observeTy (depth + 1) (quoteLayer assignment layer) =
      layer.evalAt (depth + 1) (fun index => Common.observeTy depth (assignment index)) :=
  quoteLayer_observe (depth + 1) assignment layer

end Yulang.CommonPresenceTailLayers
