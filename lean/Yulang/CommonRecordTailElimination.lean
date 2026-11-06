import Yulang.CommonTailElimination

/-!
# Exact elimination of common record-tail constructor equations

A record's same-depth tail is a positive unary Boolean operation at every
observation. Its value at false and true is represented by the same record
with top and bottom tails. Consequently

`record l A R ≈ inter (record l A top) (union (record l A bottom) R)`.

The fixed head and record shape are retained even when the tail is bottom.
This is why the data-demand shortcut `inter (required l A) (mask [l] R)` is
not used here. The alternative formula with a masked tail and required-bottom
guard is longer and introduces a synthetic mask; the two endpoint records
need no new coordinate. Payloads and parameters remain arbitrary common types.

The executable compiler below lowers actual record constructors, including
arbitrary unguarded record-tail cycles, into the previously solved positive
masked equations. Its independent model relation interprets the original
constructors directly. It does not include a default whose source is an
unknown same-depth tail: default also changes the queried observation, from
required to optional and to presence, and needs a separate compilation.
-/

namespace Yulang.CommonFinite

universe u
variable {Row : Type u} {leRow : Row → Row → Prop} {env : Environment Row}
  {argumentOrder : Ty Row → Ty Row → Prop}

theorem maskedProbeStep_record_polynomial (hidden : List Nat) (label : Nat)
    (payload tail : Ty Row) (obs : Observation Row) :
    MaskedProbeStep leRow env argumentOrder hidden (.record label payload tail) obs ↔
      MaskedProbeStep leRow env argumentOrder hidden (.record label payload .top) obs ∨
        (MaskedProbeStep leRow env argumentOrder hidden (.record label payload .bottom) obs ∧
          MaskedProbeStep leRow env argumentOrder hidden tail obs) := by
  cases obs with
  | field query obs =>
      simp only [MaskedProbeStep]
      split
      · exact ⟨Or.inl, fun accepted => accepted.elim id And.left⟩
      · simp
  | optional query obs =>
      simp only [MaskedProbeStep]
      split
      · exact ⟨Or.inl, fun accepted => accepted.elim id And.left⟩
      · simp only [false_or, true_or, true_and]
        exact or_comm
  | role name => exact ⟨Or.inl, fun accepted => accepted.elim id And.left⟩
  | _ => simp [MaskedProbeStep]

theorem maskedProbeAt_record_polynomial (rank : Nat) (env : Environment Row)
    (hidden : List Nat) (label : Nat) (payload tail : Ty Row) (obs : Observation Row) :
    MaskedProbeAt leRow rank env hidden (.record label payload tail) obs ↔
      MaskedProbeAt leRow rank env hidden (.record label payload .top) obs ∨
        (MaskedProbeAt leRow rank env hidden (.record label payload .bottom) obs ∧
          MaskedProbeAt leRow rank env hidden tail obs) := by
  cases rank <;> exact maskedProbeStep_record_polynomial hidden label payload tail obs

theorem producerEq_record_polynomial (label : Nat) (payload tail : Ty Row) :
    ProducerEq leRow (.record label payload tail)
      (.inter (.record label payload .top) (.union (.record label payload .bottom) tail)) := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  have same := maskedProbeAt_record_polynomial (leRow := leRow) rank env [] label payload tail obs
  simpa only [maskedProbeAt_nil, probeAt_inter, probeAt_union] using same

end Yulang.CommonFinite

namespace Yulang.CommonTailElimination

theorem read_record_polynomial (depth rank : Nat) (env : CommonFinite.Environment Common.Row)
    (hidden : List Nat) (label : Nat) (payload tail : Common.Ty) (obs : Common.Observation) :
    Read depth rank env hidden (Common.record label payload tail) obs ↔
      Read depth rank env hidden (Common.record label payload .top) obs ∨
        (Read depth rank env hidden (Common.record label payload .bottom) obs ∧
          Read depth rank env hidden tail obs) :=
  CommonFinite.maskedProbeAt_record_polynomial rank env hidden label _ _ obs

end Yulang.CommonTailElimination

namespace Yulang.Common

theorem common_record_polynomial (label : Nat) (payload tail : Ty) :
    Equivalent (record label payload tail)
      (.inter (record label payload .top) (.union (record label payload .bottom) tail)) :=
  ⟨fun _ => CommonFinite.producerEq_record_polynomial label _ _ |>.1,
    fun _ => CommonFinite.producerEq_record_polynomial label _ _ |>.2⟩

end Yulang.Common

namespace Yulang.CommonRecordTailElimination

open Common (Ty)
open PresenceTailElimination (Mask Coordinate)
open CommonTailElimination (Read read_mask read_union read_inter read_mask_congr)

variable {slots labels : Nat}

inductive Body (slots labels : Nat) where
  | atom : Ty → Body slots labels
  | ref : Fin slots → Body slots labels
  | union : Body slots labels → Body slots labels → Body slots labels
  | inter : Body slots labels → Body slots labels → Body slots labels
  | mask : Mask labels → Body slots labels → Body slots labels
  | record : Nat → Ty → Body slots labels → Body slots labels

namespace Body

/-- Independent direct constructor substitution. The record tail stays at
the same depth, and the payload is an arbitrary fixed common type. -/
def eval (solution : Fin slots → Ty) : Body slots labels → Ty
  | .atom type => type
  | .ref index => solution index
  | .union first last => .union (eval solution first) (eval solution last)
  | .inter first last => .inter (eval solution first) (eval solution last)
  | .mask hidden body => Common.mask hidden.names (eval solution body)
  | .record label payload tail => Common.record label payload (eval solution tail)

/-- A finite compiler that keeps every shared reference and mask index. -/
def compile : Body slots labels → CommonTailElimination.Body slots labels
  | .atom type => .atom type
  | .ref index => .ref index
  | .union first last => .union (compile first) (compile last)
  | .inter first last => .inter (compile first) (compile last)
  | .mask hidden body => .mask hidden (compile body)
  | .record label payload tail =>
      .inter (.atom (Common.record label payload .top))
        (.union (.atom (Common.record label payload .bottom)) (compile tail))

theorem read_compile (body : Body slots labels) (solution : Fin slots → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) (hidden : Mask labels) :
    Read depth rank env outer
        (body.compile.expand (CommonTailElimination.seed solution) hidden) obs ↔
      Read depth rank env (outer ++ hidden.names) (body.eval solution) obs := by
  induction body generalizing hidden with
  | atom | ref => exact read_mask depth rank env outer hidden.names _ obs
  | union first last ihf ihl =>
      simp only [compile, CommonTailElimination.Body.expand, eval, read_union]
      exact and_congr (ihf hidden) (ihl hidden)
  | inter first last ihf ihl =>
      simp only [compile, CommonTailElimination.Body.expand, eval, read_inter]
      exact or_congr (ihf hidden) (ihl hidden)
  | mask more body ih =>
      simp only [compile, CommonTailElimination.Body.expand, eval, read_mask]
      refine (ih (hidden.join more)).trans ?_
      apply read_mask_congr
      intro label
      simp only [List.mem_append, Mask.mem_names_join]
      exact or_assoc.symm
  | record label payload tail ih =>
      simp only [compile, CommonTailElimination.Body.expand, eval, read_inter, read_union, read_mask]
      exact (or_congr Iff.rfl (and_congr Iff.rfl (ih hidden))).trans
        (CommonTailElimination.read_record_polynomial depth rank env (outer ++ hidden.names)
          label payload (tail.eval solution) obs).symm

end Body

abbrev Graph (slots labels : Nat) := Fin slots → Body slots labels

def compile (graph : Graph slots labels) : CommonTailElimination.Graph slots labels :=
  fun index => (graph index).compile

/-- Constructor equations on the original graph, with no solver object or
residual certificate in the definition. -/
def Models (graph : Graph slots labels) (solution : Fin slots → Ty) : Prop :=
  ∀ index, Common.Equivalent ((graph index).eval solution) (solution index)

theorem compile_step_read (graph : Graph slots labels) (solution : Fin slots → Ty)
    (depth rank : Nat) (env : CommonFinite.Environment Common.Row) (outer : List Nat)
    (obs : Common.Observation) (coordinate : Coordinate slots labels) :
    CommonTailElimination.semanticStep (compile graph) depth rank env outer obs
        (CommonTailElimination.observeFamily depth rank env outer obs
          (CommonTailElimination.seed solution)) coordinate ↔
      Read depth rank env (outer ++ coordinate.2.names) ((graph coordinate.1).eval solution) obs :=
  ((graph coordinate.1).compile.read_expand (CommonTailElimination.seed solution)
    depth rank env outer obs coordinate.2).symm.trans
      ((graph coordinate.1).read_compile solution depth rank env outer obs coordinate.2)

theorem compile_models_exact (graph : Graph slots labels) (solution : Fin slots → Ty) :
    CommonTailElimination.Satisfies (compile graph) solution ↔ Models graph solution := by
  constructor
  · intro valid
    apply (CommonTailElimination.maskedEquivalent_iff_common _ _).mp
    intro depth rank env outer index obs
    have fixed := congrFun (valid depth rank env outer obs) (index, Mask.empty)
    have readBody := compile_step_read graph solution depth rank env outer obs (index, Mask.empty)
    have same := readBody.symm.trans (Iff.of_eq fixed)
    simpa only [CommonTailElimination.observeFamily, CommonTailElimination.seed,
      read_mask, Mask.names_empty, List.append_nil] using same
  · intro valid depth rank env outer obs
    have same := (CommonTailElimination.maskedEquivalent_iff_common _ _).mpr valid
    funext coordinate
    apply propext
    exact (compile_step_read graph solution depth rank env outer obs coordinate).trans
      ((same depth rank env (outer ++ coordinate.2.names) coordinate.1 obs).trans
        (read_mask depth rank env outer coordinate.2.names (solution coordinate.1) obs).symm)

def solve (graph : Graph slots labels) (parameters : Fin slots → Ty) : Fin slots → Ty :=
  CommonTailElimination.solve (compile graph) parameters

theorem solve_models (graph : Graph slots labels) (parameters : Fin slots → Ty) :
    Models graph (solve graph parameters) :=
  (compile_models_exact graph _).mp (CommonTailElimination.solve_satisfies (compile graph) parameters)

theorem solve_retract (graph : Graph slots labels) (solution : Fin slots → Ty)
    (valid : Models graph solution) (index : Fin slots) :
    Common.Equivalent (solve graph solution index) (solution index) :=
  CommonTailElimination.solve_retract_common (compile graph) solution
    ((compile_models_exact graph solution).mpr valid) index

/-- Every input record-tail graph and every independent common assignment
are covered. Its exact solution family uses unrestricted common types as
parameters and imposes no residual equations, support or fuel premise. -/
theorem solved_instances_exact (graph : Graph slots labels) (solution : Fin slots → Ty) :
    Models graph solution ↔
      ∃ parameters : Fin slots → Ty,
        ∀ index, Common.Equivalent (solve graph parameters index) (solution index) :=
  (compile_models_exact graph solution).symm.trans
    (CommonTailElimination.common_solved_instances_exact (compile graph) solution)

end Yulang.CommonRecordTailElimination
