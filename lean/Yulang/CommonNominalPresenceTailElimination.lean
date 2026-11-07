import Yulang.CommonNominalRecordTailElimination
import Yulang.CommonNominalDefault

/-!
# Free common solutions of record/default same-depth equations

The original equation bodies contain actual record constructors and whole
defaults. Their payloads and fallbacks are arbitrary fixed common types;
same-depth references occur positively in tails and default sources.

The executable solver iterates type intersection, then type union. A finite
Boolean interpretation proves the iteration bound: for each observation it
tracks every slot, every finite mask and four field modes (the original
query, its optional query, presence, and optional presence). Default changes
only among those four modes. No semantic law or successful solver result is
part of the input.
-/

namespace Yulang.CommonNominalPresenceTailElimination

open CommonNominalCarrier (Ty)
open CommonNominalTailElimination (Read read_mask read_union read_inter read_mask_congr)
open PresenceTailElimination (Mask Coordinate coordinates coordinates_complete)
open PositiveEquationElimination (Valuation Below Monotone iterate)

variable {slots labels : Nat}

inductive Mode where
  | keep | optional | present | optionalPresent
  deriving DecidableEq, Repr

def Mode.observe (mode : Mode) (obs : CommonNominalCarrier.Observation) : CommonNominalCarrier.Observation :=
  match mode with
  | .keep => obs
  | .optional => match obs with
      | .field label payload | .optional label payload => .optional label payload
      | other => other
  | .present => match obs with
      | .field label _ | .optional label _ => .field label .trivial
      | other => other
  | .optionalPresent => match obs with
      | .field label _ | .optional label _ => .optional label .trivial
      | other => other

def Mode.toOptional : Mode → Mode
  | .keep | .optional => .optional
  | .present | .optionalPresent => .optionalPresent

def modes : List Mode := [.keep, .optional, .present, .optionalPresent]

theorem modes_complete (mode : Mode) : mode ∈ modes := by
  cases mode <;> simp [modes]

abbrev ObservationCoordinate (slots labels : Nat) := Coordinate slots labels × Mode

def observationCoordinates (slots labels : Nat) : List (ObservationCoordinate slots labels) :=
  (coordinates slots labels).flatMap fun coordinate => modes.map (coordinate, ·)

theorem observationCoordinates_complete (coordinate : ObservationCoordinate slots labels) :
    coordinate ∈ observationCoordinates slots labels := by
  simp only [observationCoordinates, List.mem_flatMap, List.mem_map]
  exact ⟨coordinate.1, coordinates_complete coordinate.1, coordinate.2,
    modes_complete coordinate.2, Prod.eta coordinate⟩

/-- A positive operation on the four observations of the whole source.
Fallback observations are constants because fallbacks are fixed payloads. -/
def defaultRead (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
    (hidden : List Nat) (current : Nat) (fallback : Ty) (obs : CommonNominalCarrier.Observation)
    (mode : Mode) (source : Mode → Prop) : Prop :=
  match mode.observe obs with
  | .field label payload =>
      if label = current ∧ current ∉ hidden then
        match depth with
        | 0 => True
        | previous + 1 => source mode.toOptional ∧
            (source .present ∨ Read previous rank env [] fallback payload)
      else source mode
  | .optional label payload =>
      (if label = current ∧ current ∉ hidden then
        match depth with
        | 0 => True
        | previous + 1 => source mode.toOptional ∧
            (source .present ∨ Read previous rank env [] fallback payload)
      else source mode) ∨ payload = .trivial
  | other => Read depth rank env hidden (CommonNominalCarrier.recordDefault current .top fallback) other

theorem defaultRead_monotone (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
    (hidden : List Nat) (current : Nat) (fallback : Ty) (obs : CommonNominalCarrier.Observation)
    (mode : Mode) (first last : Mode → Prop) (below : ∀ mode, first mode → last mode) :
    defaultRead depth rank env hidden current fallback obs mode first →
      defaultRead depth rank env hidden current fallback obs mode last := by
  cases found : mode.observe obs with
  | field label payload =>
      simp only [defaultRead, found]
      by_cases active : label = current ∧ current ∉ hidden
      · simp only [active]
        cases depth with
        | zero => exact id
        | succ previous =>
            exact And.imp (below mode.toOptional) (Or.imp (below .present) id)
      · simpa only [active, ↓reduceIte] using below mode
  | optional label payload =>
      simp only [defaultRead, found]
      apply Or.imp _ id
      by_cases active : label = current ∧ current ∉ hidden
      · simp only [active]
        cases depth with
        | zero => exact id
        | succ previous =>
            exact And.imp (below mode.toOptional) (Or.imp (below .present) id)
      · simpa only [active, ↓reduceIte] using below mode
  | _ => simp only [defaultRead, found]; exact id

private theorem masked_bottom (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
    (argumentOrder : CommonNominalFinite.Ty CommonNominalCarrier.Row → CommonNominalFinite.Ty CommonNominalCarrier.Row → Prop)
    (hidden : List Nat) (obs : CommonNominalCarrier.Observation) :
    CommonNominalFinite.MaskedProbeStep Common.rowLe env argumentOrder hidden .bottom obs := by
  cases obs <;> trivial

private theorem implication_or_constant (condition first last : Prop) [Decidable condition] :
    (condition → first ∨ last) ↔ (condition → first) ∨ last := by
  by_cases holds : condition <;> simp [holds]

/-- Mode changes are exact for arbitrary regular sources, fallbacks and
outer masks, including the depth-zero record approximation of a default. -/
theorem read_default_modes (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
    (hidden : List Nat) (current : Nat) (source fallback : Ty) (obs : CommonNominalCarrier.Observation)
    (mode : Mode) :
    Read depth rank env hidden (CommonNominalCarrier.recordDefault current source fallback) (mode.observe obs) ↔
      defaultRead depth rank env hidden current fallback obs mode
        (fun next => Read depth rank env hidden source (next.observe obs)) := by
  cases obs <;> cases mode <;> cases depth <;> cases rank <;>
    simp [defaultRead, Mode.observe, Mode.toOptional, Read, CommonNominalCarrier.recordDefault, CommonNominalCarrier.observeTy,
      CommonNominalSyntax.Layer.evalAt, CommonNominalSyntax.observe, CommonNominalSyntax.graph,
      CommonNominalFinite.MaskedProbeAt, CommonNominalFinite.MaskedProbeStep, masked_bottom]
  all_goals exact implication_or_constant _ _ _

inductive Body (slots labels : Nat) where
  | atom : Ty → Body slots labels
  | ref : Fin slots → Body slots labels
  | union : Body slots labels → Body slots labels → Body slots labels
  | inter : Body slots labels → Body slots labels → Body slots labels
  | mask : Mask labels → Body slots labels → Body slots labels
  | record : Nat → Ty → Body slots labels → Body slots labels
  | recordDefault : Nat → Body slots labels → Ty → Body slots labels

namespace Body

/-- Direct substitution into the original constructors. No solver syntax is
used in the independently stated equation semantics. -/
def eval (solution : Fin slots → Ty) : Body slots labels → Ty
  | .atom type => type
  | .ref index => solution index
  | .union first last => .union (eval solution first) (eval solution last)
  | .inter first last => .inter (eval solution first) (eval solution last)
  | .mask hidden body => CommonNominalCarrier.mask hidden.names (eval solution body)
  | .record label payload tail => CommonNominalCarrier.record label payload (eval solution tail)
  | .recordDefault label source fallback => CommonNominalCarrier.recordDefault label (eval solution source) fallback

def evalRead (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
    (outer : List Nat) (obs : CommonNominalCarrier.Observation)
    (family : Valuation (ObservationCoordinate slots labels)) (hidden : Mask labels) (mode : Mode) :
    Body slots labels → Prop
  | .atom type => Read depth rank env (outer ++ hidden.names) type (mode.observe obs)
  | .ref index => family ((index, hidden), mode)
  | .union first last => evalRead depth rank env outer obs family hidden mode first ∧
      evalRead depth rank env outer obs family hidden mode last
  | .inter first last => evalRead depth rank env outer obs family hidden mode first ∨
      evalRead depth rank env outer obs family hidden mode last
  | .mask more body => evalRead depth rank env outer obs family (hidden.join more) mode body
  | .record label payload tail =>
      Read depth rank env (outer ++ hidden.names) (CommonNominalCarrier.record label payload .top) (mode.observe obs) ∨
        (Read depth rank env (outer ++ hidden.names) (CommonNominalCarrier.record label payload .bottom) (mode.observe obs) ∧
          evalRead depth rank env outer obs family hidden mode tail)
  | .recordDefault label source fallback =>
      defaultRead depth rank env (outer ++ hidden.names) label fallback obs mode
        (fun next => evalRead depth rank env outer obs family hidden next source)

theorem evalRead_monotone (body : Body slots labels) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat) (obs : CommonNominalCarrier.Observation)
    (first last : Valuation (ObservationCoordinate slots labels)) (below : Below first last)
    (hidden : Mask labels) (mode : Mode) :
    body.evalRead depth rank env outer obs first hidden mode →
      body.evalRead depth rank env outer obs last hidden mode := by
  induction body generalizing hidden mode with
  | atom => exact id
  | ref index => exact below ((index, hidden), mode)
  | union first last ihf ihl => exact And.imp (ihf hidden mode) (ihl hidden mode)
  | inter first last ihf ihl => exact Or.imp (ihf hidden mode) (ihl hidden mode)
  | mask more body ih => exact ih (hidden.join more) mode
  | record label payload tail ih => exact Or.imp id (And.imp id (ih hidden mode))
  | recordDefault label source fallback ih =>
      exact defaultRead_monotone depth rank env _ label fallback obs mode _ _ (ih hidden)

theorem read_eval (body : Body slots labels) (solution : Fin slots → Ty)
    (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat)
    (obs : CommonNominalCarrier.Observation) (hidden : Mask labels) (mode : Mode) :
    Read depth rank env (outer ++ hidden.names) (body.eval solution) (mode.observe obs) ↔
      body.evalRead depth rank env outer obs
        (fun coordinate => Read depth rank env (outer ++ coordinate.1.2.names)
          (solution coordinate.1.1) (coordinate.2.observe obs)) hidden mode := by
  induction body generalizing hidden mode with
  | atom | ref => rfl
  | union first last ihf ihl =>
      exact (read_union depth rank env _ _ _ _).trans (and_congr (ihf hidden mode) (ihl hidden mode))
  | inter first last ihf ihl =>
      exact (read_inter depth rank env _ _ _ _).trans (or_congr (ihf hidden mode) (ihl hidden mode))
  | mask more body ih =>
      simp only [eval, read_mask, evalRead]
      refine (read_mask_congr depth rank env _ _ ?_ _ _).trans (ih (hidden.join more) mode)
      intro label
      simp only [List.mem_append, Mask.mem_names_join]
      exact or_assoc
  | record label payload tail ih =>
      exact (CommonNominalTailElimination.read_record_polynomial depth rank env _ label payload _ _).trans
        (or_congr Iff.rfl (and_congr Iff.rfl (ih hidden mode)))
  | recordDefault label source fallback ih =>
      have sourceEq : (fun next => Read depth rank env (outer ++ hidden.names)
          (source.eval solution) (next.observe obs)) =
        (fun next => source.evalRead depth rank env outer obs
          (fun coordinate => Read depth rank env (outer ++ coordinate.1.2.names)
            (solution coordinate.1.1) (coordinate.2.observe obs)) hidden next) := by
        funext next
        exact propext (ih hidden next)
      exact (read_default_modes depth rank env _ label _ fallback obs mode).trans
        (Iff.of_eq (congrArg (defaultRead depth rank env _ label fallback obs mode) sourceEq))

end Body

abbrev Graph (slots labels : Nat) := Fin slots → Body slots labels

def step (graph : Graph slots labels) (family : Fin slots → Ty) : Fin slots → Ty :=
  fun index => (graph index).eval family

def ascend (graph : Graph slots labels) (family : Fin slots → Ty) : Fin slots → Ty :=
  fun index => .inter (family index) (step graph family index)

def descend (graph : Graph slots labels) (family : Fin slots → Ty) : Fin slots → Ty :=
  fun index => .union (family index) (step graph family index)

/-- The finite capacity counts slots, masks and four observation modes. It
is derived from the input signature, never supplied as search fuel. -/
def solve (graph : Graph slots labels) (parameters : Fin slots → Ty) : Fin slots → Ty :=
  iterate (descend graph) (observationCoordinates slots labels).length
    (iterate (ascend graph) (observationCoordinates slots labels).length parameters)

def observeFamily (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row)
    (outer : List Nat) (obs : CommonNominalCarrier.Observation) (family : Fin slots → Ty) :
    Valuation (ObservationCoordinate slots labels) :=
  fun coordinate => Read depth rank env (outer ++ coordinate.1.2.names)
    (family coordinate.1.1) (coordinate.2.observe obs)

def semanticStep (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat) (obs : CommonNominalCarrier.Observation) :
    Valuation (ObservationCoordinate slots labels) → Valuation (ObservationCoordinate slots labels) :=
  fun family coordinate => (graph coordinate.1.1).evalRead depth rank env outer obs
    family coordinate.1.2 coordinate.2

theorem semanticStep_monotone (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat) (obs : CommonNominalCarrier.Observation) :
    Monotone (semanticStep graph depth rank env outer obs) :=
  fun first last below coordinate =>
    (graph coordinate.1.1).evalRead_monotone depth rank env outer obs first last below
      coordinate.1.2 coordinate.2

theorem observe_step (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat) (obs : CommonNominalCarrier.Observation)
    (family : Fin slots → Ty) :
    observeFamily depth rank env outer obs (step graph family) =
      semanticStep graph depth rank env outer obs (observeFamily depth rank env outer obs family) := by
  funext coordinate
  exact propext ((graph coordinate.1.1).read_eval family depth rank env outer obs
    coordinate.1.2 coordinate.2)

theorem observe_ascend (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat) (obs : CommonNominalCarrier.Observation)
    (family : Fin slots → Ty) :
    observeFamily depth rank env outer obs (ascend graph family) =
      PositiveEquationElimination.ascend (semanticStep graph depth rank env outer obs)
        (observeFamily depth rank env outer obs family) := by
  funext coordinate
  apply propext
  exact (read_inter depth rank env _ _ _ _).trans
    (or_congr Iff.rfl (Iff.of_eq (congrFun (observe_step graph depth rank env outer obs family) coordinate)))

theorem observe_descend (graph : Graph slots labels) (depth rank : Nat)
    (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat) (obs : CommonNominalCarrier.Observation)
    (family : Fin slots → Ty) :
    observeFamily depth rank env outer obs (descend graph family) =
      PositiveEquationElimination.descend (semanticStep graph depth rank env outer obs)
        (observeFamily depth rank env outer obs family) := by
  funext coordinate
  apply propext
  exact (read_union depth rank env _ _ _ _).trans
    (and_congr Iff.rfl (Iff.of_eq (congrFun (observe_step graph depth rank env outer obs family) coordinate)))

theorem observe_solve (graph : Graph slots labels) (parameters : Fin slots → Ty)
    (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat)
    (obs : CommonNominalCarrier.Observation) :
    observeFamily depth rank env outer obs (solve graph parameters) =
      PositiveEquationElimination.project (observationCoordinates slots labels)
        (semanticStep graph depth rank env outer obs)
        (observeFamily depth rank env outer obs parameters) := by
  unfold solve PositiveEquationElimination.project
  rw [PositiveEquationElimination.iterate_commute (descend graph)
    (PositiveEquationElimination.descend (semanticStep graph depth rank env outer obs))
    (observeFamily depth rank env outer obs) (observe_descend graph depth rank env outer obs)]
  rw [PositiveEquationElimination.iterate_commute (ascend graph)
    (PositiveEquationElimination.ascend (semanticStep graph depth rank env outer obs))
    (observeFamily depth rank env outer obs) (observe_ascend graph depth rank env outer obs)]

/-- The original equation semantics uses ordinary common equivalence, with
no fixed-point witness, mask certificate or solver result in its definition. -/
def Models (graph : Graph slots labels) (solution : Fin slots → Ty) : Prop :=
  ∀ index, CommonNominalCarrier.Equivalent ((graph index).eval solution) (solution index)

theorem models_iff_observe_fixed (graph : Graph slots labels) (solution : Fin slots → Ty) :
    Models graph solution ↔
      ∀ depth rank env outer obs,
        semanticStep graph depth rank env outer obs
          (observeFamily depth rank env outer obs solution) =
            observeFamily depth rank env outer obs solution := by
  constructor
  · intro valid depth rank env outer obs
    have same := (CommonNominalTailElimination.maskedEquivalent_iff_common _ _).mpr valid
    funext coordinate
    apply propext
    exact ((graph coordinate.1.1).read_eval solution depth rank env outer obs
      coordinate.1.2 coordinate.2).symm.trans
        (same depth rank env (outer ++ coordinate.1.2.names) coordinate.1.1 (coordinate.2.observe obs))
  · intro fixed
    apply (CommonNominalTailElimination.maskedEquivalent_iff_common _ _).mp
    intro depth rank env outer index obs
    have same := congrFun (fixed depth rank env outer obs) ((index, Mask.empty), Mode.keep)
    have body := (graph index).read_eval solution depth rank env outer obs Mask.empty .keep
    simpa only [observeFamily, Mask.names_empty, List.append_nil, Mode.observe] using
      body.trans (Iff.of_eq same)

/-- Every unrestricted common parameter assignment solves the original
record/default equations. Unguarded same-depth cycles are included. -/
theorem solve_models (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Models graph (solve graph parameters) := by
  apply (models_iff_observe_fixed graph _).mpr
  intro depth rank env outer obs
  rw [observe_solve]
  exact PositiveEquationElimination.project_sound (observationCoordinates slots labels)
    observationCoordinates_complete (semanticStep graph depth rank env outer obs)
    (semanticStep_monotone graph depth rank env outer obs) _

theorem observeFamily_equivalent (first last : Fin slots → Ty)
    (same : ∀ index, CommonNominalCarrier.Equivalent (first index) (last index))
    (depth rank : Nat) (env : CommonNominalFinite.Environment CommonNominalCarrier.Row) (outer : List Nat)
    (obs : CommonNominalCarrier.Observation) :
    observeFamily (labels := labels) depth rank env outer obs first =
      observeFamily depth rank env outer obs last := by
  have masked := (CommonNominalTailElimination.maskedEquivalent_iff_common first last).mpr same
  funext coordinate
  exact propext (masked depth rank env (outer ++ coordinate.1.2.names)
    coordinate.1.1 (coordinate.2.observe obs))

theorem models_congr (graph : Graph slots labels) (first last : Fin slots → Ty)
    (same : ∀ index, CommonNominalCarrier.Equivalent (first index) (last index)) :
    Models graph first ↔ Models graph last := by
  rw [models_iff_observe_fixed, models_iff_observe_fixed]
  simp only [observeFamily_equivalent first last same]

/-- Every independently given solution is recovered using that very
solution as the unconstrained parameter assignment. -/
theorem solve_retract (graph : Graph slots labels) (solution : Fin slots → Ty)
    (valid : Models graph solution) (index : Fin slots) :
    CommonNominalCarrier.Equivalent (solve graph solution index) (solution index) := by
  apply CommonNominalTailElimination.maskedEquivalent_common (solve graph solution) solution _ index
  intro depth rank env outer actual obs
  have fixed := (models_iff_observe_fixed graph solution).mp valid depth rank env outer obs
  have retracted : observeFamily depth rank env outer obs (solve graph solution) =
      observeFamily (labels := labels) depth rank env outer obs solution := by
    rw [observe_solve]
    exact PositiveEquationElimination.project_retract _ _ _ fixed
  have atIndex := congrFun retracted ((actual, Mask.empty), Mode.keep)
  simpa only [observeFamily, Mask.names_empty, List.append_nil, Mode.observe] using Iff.of_eq atIndex

/-- Every finite original graph and every independent solution assignment
are covered. The right side has only free common parameters and common
equivalence; no existential constraints or successful-run premise remains. -/
theorem solved_instances_exact (graph : Graph slots labels) (solution : Fin slots → Ty) :
    Models graph solution ↔
      ∃ parameters : Fin slots → Ty,
        ∀ index, CommonNominalCarrier.Equivalent (solve graph parameters index) (solution index) := by
  constructor
  · intro valid
    exact ⟨solution, solve_retract graph solution valid⟩
  · rintro ⟨parameters, same⟩
    exact (models_congr graph (solve graph parameters) solution same).mp (solve_models graph parameters)

end Yulang.CommonNominalPresenceTailElimination
