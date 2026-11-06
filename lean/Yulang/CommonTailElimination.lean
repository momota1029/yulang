import Yulang.Common
import Yulang.CommonFiniteMask
import Yulang.PresenceTailElimination

/-!
# Free common-type solutions of same-depth masked positive equations

The atoms and free parameters are actual finite/regular `Common.Ty` values.
They may contain arbitrary functions, rows, defaults and recursive payloads.
Only the same-depth reference grammar is positive: references, union,
intersection and masks. The recursive body semantics is independent of the
solver. Every finite input graph is solved, including unguarded tail cycles.

Producer union intersects accepted observations and producer intersection
unites them. Consequently the inflationary phase uses type intersection and
the deflationary phase uses type union. This duality is proved against the
concrete common probes, not assumed as a field in a solver model.

This module does not lower record/default source constructors or arbitrary
inequality graphs into these equations. In particular the data-demand recipe
`required ∩ masked-tail` is not identified with a common producer record.
-/

namespace Yulang.CommonTailElimination

open Common (Ty)
open PresenceTailElimination (Mask Coordinate coordinates coordinates_complete)
open PositiveEquationElimination (Valuation Below Monotone iterate)

variable {slots labels : Nat}

/-- No solver output occurs in this observation of a concrete common type. -/
def Read (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (hidden : List Nat) (type : Ty) (obs : Common.Observation) : Prop :=
  CommonFinite.MaskedProbeAt Common.rowLe rank env hidden (Common.observeTy depth type) obs

@[simp] theorem read_union (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (hidden : List Nat) (first last : Ty) (obs : Common.Observation) :
    Read depth rank env hidden (.union first last) obs ↔
      Read depth rank env hidden first obs ∧ Read depth rank env hidden last obs := by
  cases rank <;> exact CommonFinite.maskedProbeStep_union hidden _ _ obs

@[simp] theorem read_inter (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (hidden : List Nat) (first last : Ty) (obs : Common.Observation) :
    Read depth rank env hidden (.inter first last) obs ↔
      Read depth rank env hidden first obs ∨ Read depth rank env hidden last obs := by
  cases rank <;> exact CommonFinite.maskedProbeStep_inter hidden _ _ obs

@[simp] theorem read_mask (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (hidden more : List Nat) (type : Ty) (obs : Common.Observation) :
    Read depth rank env hidden (Common.mask more type) obs ↔
      Read depth rank env (hidden ++ more) type obs :=
  CommonFinite.maskedProbeAt_mask rank env hidden more _ obs

theorem read_mask_congr (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (first last : List Nat) (same : ∀ label, label ∈ first ↔ label ∈ last)
    (type : Ty) (obs : Common.Observation) :
    Read depth rank env first type obs ↔ Read depth rank env last type obs :=
  CommonFinite.maskedProbeAt_congr rank env first last same _ obs

inductive Body (slots labels : Nat) where
  | atom : Ty → Body slots labels
  | ref : Fin slots → Body slots labels
  | union : Body slots labels → Body slots labels → Body slots labels
  | inter : Body slots labels → Body slots labels → Body slots labels
  | mask : Mask labels → Body slots labels → Body slots labels

namespace Body

def expand (tails : Coordinate slots labels → Ty) (hidden : Mask labels) :
    Body slots labels → Ty
  | .atom type => Common.mask hidden.names type
  | .ref index => tails (index, hidden)
  | .union first last => .union (expand tails hidden first) (expand tails hidden last)
  | .inter first last => .inter (expand tails hidden first) (expand tails hidden last)
  | .mask more body => expand tails (hidden.join more) body

/-- Pointwise positive equations over accepted probes. The two lattice
connectives are dual to ordinary data membership, as the interpreter requires. -/
def eval (atoms : Ty → Mask labels → Prop) (tails : Valuation (Coordinate slots labels))
    (hidden : Mask labels) : Body slots labels → Prop
  | .atom type => atoms type hidden
  | .ref index => tails (index, hidden)
  | .union first last => eval atoms tails hidden first ∧ eval atoms tails hidden last
  | .inter first last => eval atoms tails hidden first ∨ eval atoms tails hidden last
  | .mask more body => eval atoms tails (hidden.join more) body

theorem eval_monotone (body : Body slots labels) (atoms : Ty → Mask labels → Prop)
    (first last : Valuation (Coordinate slots labels)) (below : Below first last)
    (hidden : Mask labels) : eval atoms first hidden body → eval atoms last hidden body := by
  induction body generalizing hidden with
  | atom => exact id
  | ref index => exact below (index, hidden)
  | union first last ihf ihl => exact And.imp (ihf hidden) (ihl hidden)
  | inter first last ihf ihl => exact Or.imp (ihf hidden) (ihl hidden)
  | mask more body ih => exact ih (hidden.join more)

theorem read_expand (body : Body slots labels) (tails : Coordinate slots labels → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) (hidden : Mask labels) :
    Read depth rank env outer (body.expand tails hidden) obs ↔
      body.eval (fun type mask => Read depth rank env outer (Common.mask mask.names type) obs)
        (fun coordinate => Read depth rank env outer (tails coordinate) obs) hidden := by
  induction body generalizing hidden with
  | atom | ref => rfl
  | union first last ihf ihl =>
      exact (read_union depth rank env outer _ _ obs).trans (and_congr (ihf hidden) (ihl hidden))
  | inter first last ihf ihl =>
      exact (read_inter depth rank env outer _ _ obs).trans (or_congr (ihf hidden) (ihl hidden))
  | mask more body ih => exact ih (hidden.join more)

end Body

abbrev Graph (slots labels : Nat) := Fin slots → Body slots labels

def seed (parameters : Fin slots → Ty) : Coordinate slots labels → Ty :=
  fun coordinate => Common.mask coordinate.2.names (parameters coordinate.1)

def step (graph : Graph slots labels) (family : Coordinate slots labels → Ty) :
    Coordinate slots labels → Ty :=
  fun coordinate => (graph coordinate.1).expand family coordinate.2

/-- Inflation in accepted observations is type intersection. -/
def ascend (graph : Graph slots labels) (family : Coordinate slots labels → Ty) :
    Coordinate slots labels → Ty :=
  fun coordinate => .inter (family coordinate) (step graph family coordinate)

/-- Deflation in accepted observations is type union. -/
def descend (graph : Graph slots labels) (family : Coordinate slots labels → Ty) :
    Coordinate slots labels → Ty :=
  fun coordinate => .union (family coordinate) (step graph family coordinate)

def solveFamily (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Coordinate slots labels → Ty :=
  iterate (descend graph) (coordinates slots labels).length
    (iterate (ascend graph) (coordinates slots labels).length (seed parameters))

def solve (graph : Graph slots labels) (parameters : Fin slots → Ty) : Fin slots → Ty :=
  fun index => solveFamily graph parameters (index, Mask.empty)

/-- A property of every independently interpreted mask, not a field carried
by a parameter or a certificate demanded from an input solution. -/
def Coherent (family : Coordinate slots labels → Ty) : Prop :=
  ∀ depth rank env outer obs index hidden more,
    Read depth rank env outer (Common.mask more.names (family (index, hidden))) obs ↔
      Read depth rank env outer (family (index, hidden.join more)) obs

theorem seed_coherent (parameters : Fin slots → Ty) :
    Coherent (seed (labels := labels) parameters) := by
  intro depth rank env outer obs index hidden more
  simp only [seed, read_mask]
  apply read_mask_congr
  intro label
  simp only [List.mem_append, Mask.mem_names_join]
  exact or_assoc.trans (or_congr Iff.rfl or_comm)

theorem Body.expand_mask (body : Body slots labels) (family : Coordinate slots labels → Ty)
    (coherent : Coherent family) (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (outer : List Nat) (obs : Common.Observation) (hidden more : Mask labels) :
    Read depth rank env outer (Common.mask more.names (body.expand family hidden)) obs ↔
      Read depth rank env outer (body.expand family (hidden.join more)) obs := by
  induction body generalizing hidden with
  | atom type =>
      simp only [expand, read_mask]
      apply read_mask_congr
      intro label
      simp only [List.mem_append, Mask.mem_names_join]
      exact or_assoc.trans (or_congr Iff.rfl or_comm)
  | ref index => exact coherent depth rank env outer obs index hidden more
  | union first last ihf ihl =>
      simpa only [expand, read_mask, read_union] using and_congr (ihf hidden) (ihl hidden)
  | inter first last ihf ihl =>
      simpa only [expand, read_mask, read_inter] using or_congr (ihf hidden) (ihl hidden)
  | mask further body ih =>
      simpa only [expand, Mask.join_right_comm hidden further more] using ih (hidden.join further)

theorem step_coherent (graph : Graph slots labels) (family : Coordinate slots labels → Ty)
    (coherent : Coherent family) : Coherent (step graph family) :=
  fun depth rank env outer obs index hidden more =>
    (graph index).expand_mask family coherent depth rank env outer obs hidden more

theorem ascend_coherent (graph : Graph slots labels) (family : Coordinate slots labels → Ty)
    (coherent : Coherent family) : Coherent (ascend graph family) := by
  intro depth rank env outer obs index hidden more
  have first := coherent depth rank env outer obs index hidden more
  have last := step_coherent graph family coherent depth rank env outer obs index hidden more
  simpa only [ascend, read_mask, read_inter] using or_congr first last

theorem descend_coherent (graph : Graph slots labels) (family : Coordinate slots labels → Ty)
    (coherent : Coherent family) : Coherent (descend graph family) := by
  intro depth rank env outer obs index hidden more
  have first := coherent depth rank env outer obs index hidden more
  have last := step_coherent graph family coherent depth rank env outer obs index hidden more
  simpa only [descend, read_mask, read_union] using and_congr first last

theorem solveFamily_coherent (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Coherent (solveFamily graph parameters) := by
  apply PresenceTailElimination.iterate_invariant (descend graph) Coherent (descend_coherent graph)
  apply PresenceTailElimination.iterate_invariant (ascend graph) Coherent (ascend_coherent graph)
  exact seed_coherent parameters

theorem solve_mask (graph : Graph slots labels) (parameters : Fin slots → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) (index : Fin slots) (hidden : Mask labels) :
    Read depth rank env outer (Common.mask hidden.names (solve graph parameters index)) obs ↔
      Read depth rank env outer (solveFamily graph parameters (index, hidden)) obs := by
  simpa only [solve, Mask.empty_join] using
    solveFamily_coherent graph parameters depth rank env outer obs index Mask.empty hidden

def semanticStep (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonFinite.Environment Common.Row) (outer : List Nat) (obs : Common.Observation) :
    Valuation (Coordinate slots labels) → Valuation (Coordinate slots labels) :=
  fun family coordinate => (graph coordinate.1).eval
    (fun type hidden => Read depth rank env outer (Common.mask hidden.names type) obs)
    family coordinate.2

def observeFamily (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (outer : List Nat) (obs : Common.Observation) (family : Coordinate slots labels → Ty) :
    Valuation (Coordinate slots labels) :=
  fun coordinate => Read depth rank env outer (family coordinate) obs

theorem semanticStep_monotone (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonFinite.Environment Common.Row) (outer : List Nat) (obs : Common.Observation) :
    Monotone (semanticStep graph depth rank env outer obs) :=
  fun first last below coordinate => (graph coordinate.1).eval_monotone _ first last below coordinate.2

theorem observe_step (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonFinite.Environment Common.Row) (outer : List Nat) (obs : Common.Observation)
    (family : Coordinate slots labels → Ty) :
    observeFamily depth rank env outer obs (step graph family) =
      semanticStep graph depth rank env outer obs (observeFamily depth rank env outer obs family) := by
  funext coordinate
  exact propext ((graph coordinate.1).read_expand family depth rank env outer obs coordinate.2)

theorem observe_ascend (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonFinite.Environment Common.Row) (outer : List Nat) (obs : Common.Observation)
    (family : Coordinate slots labels → Ty) :
    observeFamily depth rank env outer obs (ascend graph family) =
      PositiveEquationElimination.ascend (semanticStep graph depth rank env outer obs)
        (observeFamily depth rank env outer obs family) := by
  funext coordinate
  apply propext
  exact (read_inter depth rank env outer _ _ obs).trans
    (or_congr Iff.rfl (Iff.of_eq (congrFun (observe_step graph depth rank env outer obs family) coordinate)))

theorem observe_descend (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonFinite.Environment Common.Row) (outer : List Nat) (obs : Common.Observation)
    (family : Coordinate slots labels → Ty) :
    observeFamily depth rank env outer obs (descend graph family) =
      PositiveEquationElimination.descend (semanticStep graph depth rank env outer obs)
        (observeFamily depth rank env outer obs family) := by
  funext coordinate
  apply propext
  exact (read_union depth rank env outer _ _ obs).trans
    (and_congr Iff.rfl (Iff.of_eq (congrFun (observe_step graph depth rank env outer obs family) coordinate)))

theorem observe_solveFamily (graph : Graph slots labels) (parameters : Fin slots → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) :
    observeFamily depth rank env outer obs (solveFamily graph parameters) =
      PositiveEquationElimination.project (coordinates slots labels)
        (semanticStep graph depth rank env outer obs)
        (observeFamily depth rank env outer obs (seed parameters)) := by
  unfold solveFamily PositiveEquationElimination.project
  rw [PositiveEquationElimination.iterate_commute (descend graph)
    (PositiveEquationElimination.descend (semanticStep graph depth rank env outer obs))
    (observeFamily depth rank env outer obs) (observe_descend graph depth rank env outer obs)]
  rw [PositiveEquationElimination.iterate_commute (ascend graph)
    (PositiveEquationElimination.ascend (semanticStep graph depth rank env outer obs))
    (observeFamily depth rank env outer obs) (observe_ascend graph depth rank env outer obs)]

theorem solveFamily_sound (graph : Graph slots labels) (parameters : Fin slots → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) :
    semanticStep graph depth rank env outer obs
        (observeFamily depth rank env outer obs (solveFamily graph parameters)) =
      observeFamily depth rank env outer obs (solveFamily graph parameters) := by
  rw [observe_solveFamily]
  exact PositiveEquationElimination.project_sound (coordinates slots labels) coordinates_complete
    (semanticStep graph depth rank env outer obs) (semanticStep_monotone graph depth rank env outer obs) _

theorem solveFamily_retract (graph : Graph slots labels) (solution : Fin slots → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation)
    (fixed : semanticStep graph depth rank env outer obs
        (observeFamily depth rank env outer obs (seed solution)) =
      observeFamily depth rank env outer obs (seed solution)) :
    observeFamily depth rank env outer obs (solveFamily graph solution) =
      observeFamily depth rank env outer obs (seed solution) := by
  rw [observe_solveFamily]
  exact PositiveEquationElimination.project_retract _ _ _ fixed

theorem observe_seed_solve (graph : Graph slots labels) (parameters : Fin slots → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) :
    observeFamily depth rank env outer obs (seed (solve graph parameters)) =
      observeFamily depth rank env outer obs (solveFamily graph parameters) := by
  funext coordinate
  exact propext (solve_mask graph parameters depth rank env outer obs coordinate.1 coordinate.2)

/-- Independent same-depth equations, at every observation and mask. -/
def Satisfies (graph : Graph slots labels) (solution : Fin slots → Ty) : Prop :=
  ∀ depth rank env outer obs,
    semanticStep graph depth rank env outer obs
        (observeFamily depth rank env outer obs (seed solution)) =
      observeFamily depth rank env outer obs (seed solution)

theorem solve_satisfies (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Satisfies graph (solve graph parameters) := by
  intro depth rank env outer obs
  rw [observe_seed_solve]
  exact solveFamily_sound graph parameters depth rank env outer obs

/-- This relation deliberately retains every outer mask. It implies common
producer equivalence, without assuming that plain equivalence is mask-stable. -/
def MaskedEquivalent (first last : Fin slots → Ty) : Prop :=
  ∀ depth rank env hidden index obs,
    Read depth rank env hidden (first index) obs ↔ Read depth rank env hidden (last index) obs

theorem seed_equivalent (first last : Fin slots → Ty) (same : MaskedEquivalent first last)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) :
    observeFamily depth rank env outer obs (seed (labels := labels) first) =
      observeFamily depth rank env outer obs (seed last) := by
  funext coordinate
  apply propext
  exact (read_mask depth rank env outer coordinate.2.names _ obs).trans
    ((same depth rank env (outer ++ coordinate.2.names) coordinate.1 obs).trans
      (read_mask depth rank env outer coordinate.2.names _ obs).symm)

theorem satisfies_congr (graph : Graph slots labels) (first last : Fin slots → Ty)
    (same : MaskedEquivalent first last) : Satisfies graph first ↔ Satisfies graph last := by
  have familySame := seed_equivalent (labels := labels) first last same
  constructor
  · intro valid depth rank env outer obs
    rw [← familySame depth rank env outer obs]
    exact valid depth rank env outer obs
  · intro valid depth rank env outer obs
    rw [familySame depth rank env outer obs]
    exact valid depth rank env outer obs

theorem solve_retract (graph : Graph slots labels) (solution : Fin slots → Ty)
    (valid : Satisfies graph solution) : MaskedEquivalent (solve graph solution) solution := by
  intro depth rank env outer index obs
  have retracted := congrFun
    (solveFamily_retract graph solution depth rank env outer obs (valid depth rank env outer obs))
    (index, Mask.empty)
  simpa only [solve, observeFamily, seed, read_mask, Mask.names_empty, List.append_nil] using
    Iff.of_eq retracted

/-- Every finite graph and every independent assignment are quantified.
Parameters on the right are unrestricted common types, with no residual
model, solver-success, closure, depth, rank or fuel condition attached. -/
theorem solved_instances_exact (graph : Graph slots labels) (solution : Fin slots → Ty) :
    Satisfies graph solution ↔
      ∃ parameters : Fin slots → Ty, MaskedEquivalent (solve graph parameters) solution := by
  constructor
  · intro valid
    exact ⟨solution, solve_retract graph solution valid⟩
  · rintro ⟨parameters, same⟩
    exact (satisfies_congr graph (solve graph parameters) solution same).mp
      (solve_satisfies graph parameters)

theorem maskedEquivalent_common (first last : Fin slots → Ty) (same : MaskedEquivalent first last)
    (index : Fin slots) : Common.Equivalent (first index) (last index) := by
  constructor <;> intro depth
  · apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have related := same depth rank env [] index obs
    simp only [Read, CommonFinite.maskedProbeAt_nil] at related
    exact related.mpr accepted
  · apply (CommonFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have related := same depth rank env [] index obs
    simp only [Read, CommonFinite.maskedProbeAt_nil] at related
    exact related.mp accepted

end Yulang.CommonTailElimination
