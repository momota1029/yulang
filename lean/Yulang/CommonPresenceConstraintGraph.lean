import Yulang.PresenceOpenTailGenerationLowering
import Yulang.PresenceSourceConstraintSupport
import Yulang.CommonRowTailInference
import Yulang.CommonPresence

/-!
# Actual presence terms as shared common equation nodes

The collector is the existing total collector for the actual presence
generator, including exact emptiness, whole defaults, arbitrary record tails,
and both negative and positive arrow children. Each collected term is lowered
to the finite body syntax consumed by `CommonRowTailInference`. Type variables
have a single shared node; row variables retain their original identifiers.

The graph has independent constructor equations and directed subtype edges.
Equations are interpreted up to common demand equivalence, so arbitrary
regular realizers, not just the canonical interpretation of the input, are
reflected. No successful inference, supported-type checker, fuel, or supplied
solution is used to construct this graph. Solving its subtype edges remains
a separate task; the equation family does not certify those edges.
-/

namespace Yulang.CommonPresenceConstraintGraph

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open PresenceOpenTailGenerationLowering (Pool subterms collect collect_covers)
open Common (Ty Row)

variable {m : Nat}

abbrev Problem := PresenceOpenTailGenerationLowering.Problem

def evaluate (rows : Fin m → Row) (values : Fin m → Ty) (term : TyTerm (Fin m)) : Ty :=
  term.eval Common.model (fun index => (values index, rows index))

def rowEval (rows : Fin m → Row) (term : RowTerm (Fin m)) : Row :=
  RowFlowSchemes.eval Common.rowAlgebra rows (PresenceSourceConstraintSupport.originalRow term)

@[simp] theorem rowEval_exact (rows : Fin m → Row) (values : Fin m → Ty)
    (term : RowTerm (Fin m)) :
    rowEval rows term = term.eval Common.model (fun index => (values index, rows index)) := by
  induction term <;> simp_all [rowEval, PresenceSourceConstraintSupport.originalRow,
    RowFlowSchemes.eval, RowTerm.eval, Common.model, Common.rowAlgebra]

def extend (pool : Pool m) (rows : Fin m → Row) (values : Fin m → Ty) : Fin pool.size → Ty :=
  fun index => evaluate rows values (pool.termAt index)

def restrict (pool : Pool m) (values : Fin pool.size → Ty) : Fin m → Ty :=
  fun index => values (pool.input index)

@[simp] theorem extend_reference (pool : Pool m) (rows : Fin m → Row) (values : Fin m → Ty)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    extend pool rows values (pool.reference term member) = evaluate rows values term := by
  simp only [extend, Pool.termAt_reference]

@[simp] theorem restrict_extend (pool : Pool m) (rows : Fin m → Row) (values : Fin m → Ty) :
    restrict pool (extend pool rows values) = values := by
  funext index
  simp only [restrict, Pool.input, extend_reference, evaluate, TyTerm.eval]

theorem input_injective (pool : Pool m) : Function.Injective pool.input := by
  intro first last same
  have equal := congrArg pool.termAt same
  simpa only [Pool.input, Pool.termAt_reference, TyTerm.var.injEq] using equal

/-- Every proper child is referenced by its shared collector index. Record
tails and default sources are same-depth references, while payloads and both
arrow children use the guarded reference positions of the actual solver. -/
def lowerNode (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    CommonRowTailInference.Body pool.size 0 m :=
  match term with
  | .var index => .ref (pool.input index)
  | .base scalar => .layer (.base scalar)
  | .bottom => .layer .bottom
  | .top => .layer .top
  | .union first last =>
      .union (.ref (pool.child _ member first (by simp [subterms])))
        (.ref (pool.child _ member last (by simp [subterms])))
  | .inter first last =>
      .inter (.ref (pool.child _ member first (by simp [subterms])))
        (.ref (pool.child _ member last (by simp [subterms])))
  | .pair first last =>
      .layer (.pair (pool.child _ member first (by simp [subterms]))
        (pool.child _ member last (by simp [subterms])))
  | .emptyRecord => .layer .emptyRecord
  | .exactEmpty => .layer .exactEmpty
  | .required label payload =>
      .recordRef label (pool.child _ member payload (by simp [subterms])) (.layer .emptyRecord)
  | .record label payload tail =>
      .recordRef label (pool.child _ member payload (by simp [subterms]))
        (.ref (pool.child _ member tail (by simp [subterms])))
  | .recordDefault label source fallback =>
      .recordDefaultRef label (.ref (pool.child _ member source (by simp [subterms])))
        (pool.child _ member fallback (by simp [subterms]))
  | .variant label payload =>
      .layer (.variant label (pool.child _ member payload (by simp [subterms])))
  | .arrow input incoming output outgoing =>
      .layer (.arrow (pool.child _ member input (by simp [subterms]))
        (PresenceSourceConstraintSupport.originalRow incoming)
        (pool.child _ member output (by simp [subterms]))
        (PresenceSourceConstraintSupport.originalRow outgoing))

def graph (pool : Pool m) : Fin pool.size → CommonRowTailInference.Body pool.size 0 m :=
  fun index => lowerNode pool (pool.termAt index) (pool.at_mem index)

@[simp] theorem graph_reference (pool : Pool m) (term : TyTerm (Fin m))
    (member : term ∈ pool.terms) :
    graph pool (pool.reference term member) = lowerNode pool term member := by
  simp only [graph, Pool.termAt_reference]

/-- Original constructor equations, before invoking any equation solver. -/
def Realizes (pool : Pool m) (rows : Fin m → Row) (values : Fin pool.size → Ty) : Prop :=
  ∀ index, Common.Equivalent ((graph pool index).eval rows values) (values index)

theorem lowerNode_extend (pool : Pool m) (rows : Fin m → Row) (values : Fin m → Ty)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    (lowerNode pool term member).eval rows (extend pool rows values) = evaluate rows values term := by
  cases term <;>
    simp only [lowerNode, CommonRowTailInference.Body.eval, CommonRowTailInference.layerAtRows,
      CommonPresenceTailLayers.quoteLayer, CommonSyntax.Layer.map, Pool.child, Pool.input,
      extend_reference, evaluate, TyTerm.eval, Common.model, Common.required,
      Common.pair, Common.emptyRecord, Common.exactEmpty, Common.variant, Common.arrow]
  case arrow input incoming output outgoing =>
    congr 1
    · exact rowEval_exact rows values incoming
    · exact rowEval_exact rows values outgoing

theorem extend_realizes (pool : Pool m) (rows : Fin m → Row) (values : Fin m → Ty) :
    Realizes pool rows (extend pool rows values) := by
  intro index
  rw [graph, lowerNode_extend]
  exact Common.equivalent_refl _

theorem realizes_reference (pool : Pool m) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    Common.Equivalent ((lowerNode pool term member).eval rows values)
      (values (pool.reference term member)) := by
  simpa only [graph_reference] using realizes (pool.reference term member)

private theorem union_congr {a b c d : Ty} (left : Common.Equivalent a b)
    (right : Common.Equivalent c d) : Common.Equivalent (.union a c) (.union b d) :=
  ⟨Common.common_union_mono left.1 right.1, Common.common_union_mono left.2 right.2⟩

private theorem inter_congr {a b c d : Ty} (left : Common.Equivalent a b)
    (right : Common.Equivalent c d) : Common.Equivalent (.inter a c) (.inter b d) :=
  ⟨Common.common_inter_mono left.1 right.1, Common.common_inter_mono left.2 right.2⟩

private theorem pair_congr {a b c d : Ty} (left : Common.Equivalent a b)
    (right : Common.Equivalent c d) : Common.Equivalent (Common.pair a c) (Common.pair b d) :=
  ⟨(Common.common_pair_iff _ _ _ _).mpr ⟨left.1, right.1⟩,
    (Common.common_pair_iff _ _ _ _).mpr ⟨left.2, right.2⟩⟩

private theorem record_congr (label : Nat) {a b c d : Ty} (left : Common.Equivalent a b)
    (right : Common.Equivalent c d) :
    Common.Equivalent (Common.record label a c) (Common.record label b d) :=
  ⟨Common.common_record_mono label left.1 right.1, Common.common_record_mono label left.2 right.2⟩

private theorem variant_congr (label : Nat) {a b : Ty} (same : Common.Equivalent a b) :
    Common.Equivalent (Common.variant label a) (Common.variant label b) :=
  ⟨(Common.common_variant_iff label _ _).mpr same.1,
    (Common.common_variant_iff label _ _).mpr same.2⟩

private theorem arrow_congr (incoming outgoing : Row) {a b c d : Ty}
    (input : Common.Equivalent a b) (output : Common.Equivalent c d) :
    Common.Equivalent (Common.arrow a incoming c outgoing) (Common.arrow b incoming d outgoing) :=
  ⟨(Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
      ⟨input.2, Common.rowLe_refl _, output.1, Common.rowLe_refl _⟩,
    (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
      ⟨input.1, Common.rowLe_refl _, output.2, Common.rowLe_refl _⟩⟩

/-- An arbitrary common regular realizer evaluates every collected source
term correctly up to demand equivalence. In particular negative arrow
children use both directions of equivalence, never a monotonicity assumption. -/
theorem realizes_evaluate (pool : Pool m) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    Common.Equivalent (values (pool.reference term member))
      (evaluate rows (restrict pool values) term) := by
  revert member
  induction term
  all_goals intro member
  all_goals have node := Common.equivalent_symm (realizes_reference pool rows values realizes _ member)
  case var index => exact Common.equivalent_refl _
  case base | bottom | top | emptyRecord | exactEmpty => exact node
  case union first last ihf ihl =>
    exact Common.equivalent_trans node (union_congr
      (ihf (pool.closed _ member first (by simp [subterms])))
      (ihl (pool.closed _ member last (by simp [subterms]))))
  case inter first last ihf ihl =>
    exact Common.equivalent_trans node (inter_congr
      (ihf (pool.closed _ member first (by simp [subterms])))
      (ihl (pool.closed _ member last (by simp [subterms]))))
  case pair first last ihf ihl =>
    exact Common.equivalent_trans node (pair_congr
      (ihf (pool.closed _ member first (by simp [subterms])))
      (ihl (pool.closed _ member last (by simp [subterms]))))
  case required label payload ih =>
    exact Common.equivalent_trans node (record_congr label
      (ih (pool.closed _ member payload (by simp [subterms]))) (Common.equivalent_refl _))
  case record label payload tail ihp iht =>
    exact Common.equivalent_trans node (record_congr label
      (ihp (pool.closed _ member payload (by simp [subterms])))
      (iht (pool.closed _ member tail (by simp [subterms]))))
  case recordDefault label source fallback ihs ihf =>
    exact Common.equivalent_trans node (Common.common_default_congr label
      (ihs (pool.closed _ member source (by simp [subterms])))
      (ihf (pool.closed _ member fallback (by simp [subterms]))))
  case variant label payload ih =>
    exact Common.equivalent_trans node (variant_congr label
      (ih (pool.closed _ member payload (by simp [subterms]))))
  case arrow input incoming output outgoing ihi iho =>
    have compared := arrow_congr (rowEval rows incoming) (rowEval rows outgoing)
      (ihi (pool.closed _ member input (by simp [subterms])))
      (iho (pool.closed _ member output (by simp [subterms])))
    have same := Common.equivalent_trans node compared
    rw [rowEval_exact rows (restrict pool values) incoming,
      rowEval_exact rows (restrict pool values) outgoing] at same
    exact same

def TypeHolds (problem : Problem m) (rows : Fin m → Row) (values : Fin m → Ty) : Prop :=
  ∀ edge ∈ problem.types,
    Common.Subtype (evaluate rows values edge.1) (evaluate rows values edge.2)

def RowsHold (constraints : List (RowTerm (Fin m) × RowTerm (Fin m)))
    (rows : Fin m → Row) : Prop :=
  ∀ edge ∈ constraints, Common.rowLe (rowEval rows edge.1) (rowEval rows edge.2)

def Holds (problem : Problem m) (rows : Fin m → Row) (values : Fin m → Ty) : Prop :=
  TypeHolds problem rows values ∧ RowsHold problem.rows rows

/-- These directed comparisons are independent of graph construction and of
equation solving. They are the remaining obligations for a subtype inspector. -/
def EdgesHold (edges : List (Fin slots × Fin slots)) (values : Fin slots → Ty) : Prop :=
  ∀ edge ∈ edges, Common.Subtype (values edge.1) (values edge.2)

theorem edgesHold_congr (edges : List (Fin slots × Fin slots)) (first last : Fin slots → Ty)
    (same : ∀ index, Common.Equivalent (first index) (last index)) :
    EdgesHold edges first ↔ EdgesHold edges last := by
  constructor
  · intro accepted edge member
    exact Common.subtype_trans (same edge.1).2
      (Common.subtype_trans (accepted edge member) (same edge.2).1)
  · intro accepted edge member
    exact Common.subtype_trans (same edge.1).1
      (Common.subtype_trans (accepted edge member) (same edge.2).2)

theorem compiled_edges_exact (problem : Problem m) (rows : Fin m → Row)
    (values : Fin problem.pool.size → Ty) (realizes : Realizes problem.pool rows values) :
    EdgesHold problem.edges values ↔ TypeHolds problem rows (restrict problem.pool values) := by
  constructor
  · intro accepted edge member
    have chosen := accepted _ (List.mem_map.mpr ⟨⟨edge, member⟩, by simp, rfl⟩)
    have first := realizes_evaluate problem.pool rows values realizes edge.1 (problem.covers edge member).1
    have last := realizes_evaluate problem.pool rows values realizes edge.2 (problem.covers edge member).2
    exact Common.subtype_trans first.2 (Common.subtype_trans chosen last.1)
  · intro accepted edge member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    have first := realizes_evaluate problem.pool rows values realizes original.val.1
      (problem.covers original.val original.property).1
    have last := realizes_evaluate problem.pool rows values realizes original.val.2
      (problem.covers original.val original.property).2
    exact Common.subtype_trans first.1
      (Common.subtype_trans (accepted original.val original.property) last.2)

/-- Finite executable graph data. The original row-slot count and all row
identifiers are preserved; only proper value subterms allocate extra nodes. -/
structure Compiled (inputs : Nat) where
  size : Nat
  definitions : Fin size → CommonRowTailInference.Body size 0 inputs
  edges : List (Fin size × Fin size)
  rows : List (RowTerm (Fin inputs) × RowTerm (Fin inputs))
  input : Fin inputs → Fin size

def compileProblem (problem : Problem m) : Compiled m where
  size := problem.pool.size
  definitions := graph problem.pool
  edges := problem.edges
  rows := problem.rows
  input := problem.pool.input

def Compiled.Realizes (compiled : Compiled m) (rows : Fin m → Row)
    (values : Fin compiled.size → Ty) : Prop :=
  ∀ index, Common.Equivalent ((compiled.definitions index).eval rows values) (values index)

def Compiled.Models (compiled : Compiled m) (rows : Fin m → Row)
    (values : Fin compiled.size → Ty) : Prop :=
  compiled.Realizes rows values ∧ EdgesHold compiled.edges values ∧ RowsHold compiled.rows rows

def Compiled.restrict (compiled : Compiled m) (values : Fin compiled.size → Ty) : Fin m → Ty :=
  fun index => values (compiled.input index)

def Compiled.readback (compiled : Compiled m) (rows : Fin m → Row)
    (values : Fin compiled.size → Ty) : Fin m → Comp Common.model :=
  fun index => (values (compiled.input index), rows index)

/-- Every semantic graph realizer, including regular graphs produced by the
equation solver, reflects its actual source inequalities and preserves rows. -/
theorem compile_models_iff (problem : Problem m) (rows : Fin m → Row)
    (values : Fin (compileProblem problem).size → Ty) :
    (compileProblem problem).Models rows values ↔
      Realizes problem.pool rows values ∧
        Holds problem rows ((compileProblem problem).restrict values) := by
  constructor
  · rintro ⟨realizes, edges, rowConstraints⟩
    exact ⟨realizes, (compiled_edges_exact problem rows values realizes).mp edges, rowConstraints⟩
  · rintro ⟨realizes, typeConstraints, rowConstraints⟩
    exact ⟨realizes, (compiled_edges_exact problem rows values realizes).mpr typeConstraints,
      rowConstraints⟩

/-- Construction needs no assignment or successful solver. At every original
row/value assignment its independent constraints are exactly the models of
the actual compiled graph whose original-variable nodes agree with it. -/
theorem compile_assignment_exact (problem : Problem m) (rows : Fin m → Row) (input : Fin m → Ty) :
    Holds problem rows input ↔
      ∃ values : Fin (compileProblem problem).size → Ty,
        (compileProblem problem).Models rows values ∧ (compileProblem problem).restrict values = input := by
  constructor
  · intro accepted
    refine ⟨extend problem.pool rows input, ?_, restrict_extend problem.pool rows input⟩
    apply (compile_models_iff problem rows _).mpr
    refine ⟨extend_realizes problem.pool rows input, ?_⟩
    change Holds problem rows (restrict problem.pool (extend problem.pool rows input))
    rw [restrict_extend]
    exact accepted
  · rintro ⟨values, models, same⟩
    have accepted := ((compile_models_iff problem rows values).mp models).2
    simpa only [same] using accepted

theorem compile_input_injective (problem : Problem m) :
    Function.Injective (compileProblem problem).input := input_injective problem.pool

open PresenceNormalForm (Atom)

/-- The actual packed atom list is split into its independent value and row
constraints. No atom, original local, result slot, or shared identifier is
removed or instantiated by this split. -/
def splitAtoms : List (Atom (Fin m)) → Problem m
  | [] => ⟨[], []⟩
  | .tyLe first last :: rest =>
      ⟨(first, last) :: (splitAtoms rest).types, (splitAtoms rest).rows⟩
  | .rowLe first last :: rest =>
      ⟨(splitAtoms rest).types, (first, last) :: (splitAtoms rest).rows⟩

theorem split_atoms_exact (atoms : List (Atom (Fin m))) (rows : Fin m → Row) (input : Fin m → Ty) :
    Holds (splitAtoms atoms) rows input ↔
      PresenceNormalForm.All Common.model (fun index => (input index, rows index)) atoms := by
  induction atoms with
  | nil => simp [Holds, TypeHolds, RowsHold, splitAtoms, PresenceNormalForm.All]
  | cons atom rest ih =>
      cases atom <;>
        simp only [splitAtoms, Holds, TypeHolds, RowsHold, List.mem_cons, forall_eq_or_imp,
          PresenceNormalForm.All, Atom.Holds, and_assoc] at *
      · simpa only [evaluate, Common.model] using and_congr_right (fun _ => ih)
      · simp only [rowEval_exact rows input, Common.model] at *
        rw [← ih]
        exact and_left_comm

def compile (atoms : List (Atom (Fin m))) : Compiled m := compileProblem (splitAtoms atoms)

/-- Every packed presence atom list has a total common graph compilation,
with exact equality on the original computations at readback. The output
still has subtype edges; it is not an inferred free-parameter scheme. -/
theorem compile_atoms_exact (atoms : List (Atom (Fin m))) (assignment : Fin m → Comp Common.model) :
    PresenceNormalForm.All Common.model assignment atoms ↔
      ∃ values : Fin (compile atoms).size → Ty,
        (compile atoms).Models (fun index => (assignment index).2) values ∧
          (compile atoms).readback (fun index => (assignment index).2) values = assignment := by
  have split := split_atoms_exact atoms (fun index => (assignment index).2) (fun index => (assignment index).1)
  have exactGraph := compile_assignment_exact (splitAtoms atoms)
    (fun index => (assignment index).2) (fun index => (assignment index).1)
  constructor
  · intro accepted
    obtain ⟨values, models, agrees⟩ := exactGraph.mp (split.mpr accepted)
    refine ⟨values, models, ?_⟩
    funext index
    exact Prod.ext (congrFun agrees index) rfl
  · rintro ⟨values, models, agrees⟩
    apply split.mp
    apply exactGraph.mpr
    refine ⟨values, models, ?_⟩
    funext index
    exact congrArg Prod.fst (congrFun agrees index)

theorem compile_atoms_reflects (atoms : List (Atom (Fin m))) (rows : Fin m → Row)
    (values : Fin (compile atoms).size → Ty) (models : (compile atoms).Models rows values) :
    PresenceNormalForm.All Common.model ((compile atoms).readback rows values) atoms :=
  (split_atoms_exact atoms rows ((compile atoms).restrict values)).mp
    ((compile_models_iff (splitAtoms atoms) rows values).mp models).2

end Yulang.CommonPresenceConstraintGraph
