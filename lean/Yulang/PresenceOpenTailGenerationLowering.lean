import Yulang.PresenceOpenTailSignature
import Yulang.TypeConstraintGraph

/-!
# Finite shared-block lowering of actual presence-generation terms

Unlike `PresenceOpenTailLowering`, this file consumes the actual
`Core.PresenceGeneration.TyTerm`, including `exactEmpty`, `required` and
`recordDefault`. The finite interpretation remains an explicit model
parameter. Full defaults are retained as their entire source image; no
field-only approximation or data-only arrow interpretation is used.

The finite source syntax supplies the same-depth expansion order. The result
is a finite regular block over arbitrary original regular input types and
rows. Every source subterm, every finite observation, and every original
type constraint are preserved and reflected. This does not construct the
finite demand/function model or eliminate the original constraints.
-/

namespace Yulang.PresenceOpenTailGenerationLowering

open Core.PresenceGeneration (Model TyTerm RowTerm Comp)
open PresenceOpenTailSignature (Layer State Ty graph model observe)

universe u v w

variable {m : Nat}

deriving instance DecidableEq for RowTerm
deriving instance DecidableEq for TyTerm

def subterms (term : TyTerm (Fin m)) : List (TyTerm (Fin m)) :=
  term :: match term with
    | .union first last | .inter first last | .pair first last
    | .record _ first last | .recordDefault _ first last | .arrow first _ last _ =>
        subterms first ++ subterms last
    | .required _ payload | .variant _ payload => subterms payload
    | _ => []

@[simp] theorem self_mem_subterms (term : TyTerm (Fin m)) : term ∈ subterms term := by
  cases term <;> simp [subterms]

theorem subterms_trans (term part child : TyTerm (Fin m))
    (inside : part ∈ subterms term) (deeper : child ∈ subterms part) : child ∈ subterms term := by
  induction term with
  | var | base | bottom | top | emptyRecord | exactEmpty =>
      have equal := List.mem_singleton.mp inside
      subst part
      exact deeper
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb
  | record _ a b iha ihb | recordDefault _ a b iha ihb | arrow a _ b _ iha ihb =>
      rcases List.mem_cons.mp inside with same | inside
      · subst part
        exact deeper
      · rcases List.mem_append.mp inside with first | last
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (iha first))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihb last))
  | required _ payload ih | variant _ payload ih =>
      rcases List.mem_cons.mp inside with same | inside
      · subst part
        exact deeper
      · exact List.mem_cons_of_mem _ (ih inside)

structure Pool (inputs : Nat) where
  terms : List (TyTerm (Fin inputs))
  distinct : terms.Nodup
  variables : ∀ index, .var index ∈ terms
  closed : ∀ term ∈ terms, ∀ part ∈ subterms term, part ∈ terms

def collect (roots : List (TyTerm (Fin m))) : Pool m where
  terms := TypeConstraintGraph.unique ((List.ofFn fun index : Fin m => TyTerm.var index) ++
    roots.flatMap subterms)
  distinct := TypeConstraintGraph.unique_nodup _
  variables := by
    intro index
    apply (TypeConstraintGraph.mem_unique _ _).mpr
    exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
  closed := by
    intro term member part inside
    apply (TypeConstraintGraph.mem_unique _ _).mpr
    have original := (TypeConstraintGraph.mem_unique _ _).mp member
    rcases List.mem_append.mp original with fromVariables | fromRoots
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp fromVariables
      have same : part = .var index := by simpa [subterms] using inside
      rw [same]
      exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
    · obtain ⟨root, present, rootContains⟩ := List.mem_flatMap.mp fromRoots
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨root, present, subterms_trans root term part rootContains inside⟩)

theorem collect_covers (roots : List (TyTerm (Fin m))) (root : TyTerm (Fin m))
    (present : root ∈ roots) : root ∈ (collect roots).terms := by
  apply (TypeConstraintGraph.mem_unique _ _).mpr
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨root, present, self_mem_subterms root⟩)

namespace Pool

def size (pool : Pool m) : Nat := pool.terms.length

def termAt (pool : Pool m) (index : Fin pool.size) : TyTerm (Fin m) := pool.terms[index.val]'index.isLt

theorem at_mem (pool : Pool m) (index : Fin pool.size) : pool.termAt index ∈ pool.terms :=
  List.getElem_mem index.isLt

def reference (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : Fin pool.size :=
  ⟨pool.terms.idxOf term, List.idxOf_lt_length_of_mem member⟩

@[simp] theorem termAt_reference (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    pool.termAt (pool.reference term member) = term :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem member)

@[simp] theorem reference_termAt (pool : Pool m) (index : Fin pool.size) :
    pool.reference (pool.termAt index) (pool.at_mem index) = index := by
  apply Fin.ext
  exact pool.distinct.idxOf_getElem index.val index.isLt

def input (pool : Pool m) (index : Fin m) : Fin pool.size := pool.reference (.var index) (pool.variables index)

def child (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (part : TyTerm (Fin m)) (inside : part ∈ subterms term) : Fin pool.size :=
  pool.reference part (pool.closed term member part inside)

end Pool

def rowEval (finite : Model.{u, v}) (rows : Fin m → finite.Row) : RowTerm (Fin m) → finite.Row
  | .var index => rows index
  | .empty => finite.empty
  | .join first last => finite.join (rowEval finite rows first) (rowEval finite rows last)

theorem rowEval_exact (finite : Model.{u, v}) (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row)
    (term : RowTerm (Fin m)) :
    rowEval finite rows term = term.eval (model finite) (fun index => (input index, rows index)) := by
  induction term with
  | var | empty => rfl
  | join first last ihf ihl => simp only [rowEval, RowTerm.eval, model, ihf, ihl]

abbrev Ref (pool : Pool m) (finite : Model.{u, v}) := Fin pool.size ⊕ State finite.Row

def lowerLayer (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) :
    (term : TyTerm (Fin m)) → term ∈ pool.terms → Layer finite.Row (Ref pool finite)
  | .var index, _ => (input index).map Sum.inr
  | .base scalar, _ => .base scalar
  | .bottom, _ => .bottom
  | .top, _ => .top
  | .union first last, member =>
      .union (lowerLayer pool finite input rows first (pool.closed _ member first (by simp [subterms])))
        (lowerLayer pool finite input rows last (pool.closed _ member last (by simp [subterms])))
  | .inter first last, member =>
      .inter (lowerLayer pool finite input rows first (pool.closed _ member first (by simp [subterms])))
        (lowerLayer pool finite input rows last (pool.closed _ member last (by simp [subterms])))
  | .pair first last, member =>
      .pair (.inl (pool.child _ member first (by simp [subterms])))
        (.inl (pool.child _ member last (by simp [subterms])))
  | .emptyRecord, _ => .emptyRecord
  | .exactEmpty, _ => .exactEmpty
  | .required label payload, member =>
      .required label (.inl (pool.child _ member payload (by simp [subterms])))
  | .record label head tail, member =>
      .record label (.inl (pool.child _ member head (by simp [subterms])))
        (lowerLayer pool finite input rows tail (pool.closed _ member tail (by simp [subterms])))
  | .recordDefault label source fallback, member =>
      .recordDefault label
        (lowerLayer pool finite input rows source (pool.closed _ member source (by simp [subterms])))
        (.inl (pool.child _ member fallback (by simp [subterms])))
  | .variant label payload, member =>
      .variant label (.inl (pool.child _ member payload (by simp [subterms])))
  | .arrow arg argRow result resultRow, member =>
      .arrow (.inl (pool.child _ member arg (by simp [subterms]))) (rowEval finite rows argRow)
        (.inl (pool.child _ member result (by simp [subterms]))) (rowEval finite rows resultRow)

def body (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row) :
    Fin pool.size → Layer finite.Row (Ref pool finite) :=
  fun index => lowerLayer pool finite input rows (pool.termAt index) (pool.at_mem index)

def evaluate (finite : Model.{u, v}) (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row)
    (term : TyTerm (Fin m)) : Ty finite.Row :=
  term.eval (model finite) (fun index => (input index, rows index))

def evaluationRef (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) : Ref pool finite → State finite.Row :=
  Sum.elim (fun index => .node (evaluate finite input rows (pool.termAt index))) id

theorem lowerLayer_map_evaluation (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    (lowerLayer pool finite input rows term member).map (evaluationRef pool finite input rows) =
      evaluate finite input rows term := by
  induction term with
  | var index =>
      simp only [lowerLayer, Layer.map_comp, evaluationRef, evaluate, TyTerm.eval]
      exact Layer.map_id _
  | base | bottom | top | emptyRecord | exactEmpty => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      simp only [lowerLayer, Layer.map, evaluate, TyTerm.eval, model, ihf, ihl]
  | pair first last | required _ first | variant _ first =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child,
        Pool.termAt_reference, evaluate, TyTerm.eval, model]
  | record label head tail ihh iht =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child, Pool.termAt_reference]
      exact congrArg (Layer.record label (.node (evaluate finite input rows head))) (iht _)
  | recordDefault label source fallback ihs ihf =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child, Pool.termAt_reference]
      exact congrArg (fun source => Layer.recordDefault label source (.node (evaluate finite input rows fallback)))
        (ihs _)
  | arrow arg argRow result resultRow =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child,
        Pool.termAt_reference, evaluate, TyTerm.eval, model]
      congr 1
      · exact rowEval_exact finite input rows argRow
      · exact rowEval_exact finite input rows resultRow

theorem evaluation_morphism (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (state : Ref pool finite) :
    ((PresenceOpenTailSignature.blockGraph (body pool finite input rows)) state).map
        (evaluationRef pool finite input rows) =
      graph finite.Row (evaluationRef pool finite input rows state) := by
  cases state with
  | inl index => exact lowerLayer_map_evaluation pool finite input rows _ _
  | inr state =>
      simp only [PresenceOpenTailSignature.blockGraph, Layer.map_comp, evaluationRef, Sum.elim_inr, id_eq]
      exact Layer.map_id _

def close (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (index : Fin pool.size) : State finite.Row :=
  PresenceOpenTailSignature.closeBlock (body pool finite input rows) index

theorem close_observe_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (index : Fin pool.size) (depth : Nat) :
    observe finite (graph finite.Row) depth (close pool finite input rows index) =
      observe finite (graph finite.Row) depth (.node (evaluate finite input rows (pool.termAt index))) := by
  have closure := PresenceOpenTailSignature.block_observe_exact finite (body pool finite input rows)
    depth (Sum.inl index)
  have evaluation := PresenceOpenTailSignature.observe_morphism finite
    (PresenceOpenTailSignature.blockGraph (body pool finite input rows)) (graph finite.Row)
    (evaluationRef pool finite input rows) (evaluation_morphism pool finite input rows) depth (Sum.inl index)
  exact closure.trans evaluation.symm

def lowerValue (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (index : Fin pool.size) : Ty finite.Row :=
  graph finite.Row (close pool finite input rows index)

theorem lowerValue_observe_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (index : Fin pool.size) (depth : Nat) :
    (lowerValue pool finite input rows index).eval finite (observe finite (graph finite.Row) depth) =
      (evaluate finite input rows (pool.termAt index)).eval finite
        (observe finite (graph finite.Row) depth) :=
  close_observe_exact pool finite input rows index (depth + 1)

def lowerTerm (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : Ty finite.Row :=
  lowerValue pool finite input rows (pool.reference term member)

/-- All constructors of the actual presence generator are covered, at all
depths and under arbitrary independent regular input values and rows. -/
theorem lowerTerm_observe_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) (depth : Nat) :
    (lowerTerm pool finite input rows term member).eval finite (observe finite (graph finite.Row) depth) =
      (evaluate finite input rows term).eval finite (observe finite (graph finite.Row) depth) := by
  have exactObservation := lowerValue_observe_exact pool finite input rows (pool.reference term member) depth
  simpa only [Pool.termAt_reference, lowerTerm] using exactObservation

/-- The equality holds before any observation of the finite carrier. Thus
every supplied family of masks/readouts is preserved, including refinements
which distinguish types with the same unmasked data meaning. -/
theorem lowerTerm_readout_exact {Observation : Sort w} (pool : Pool m) (finite : Model.{u, v})
    (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) (depth : Nat)
    (readout : List Nat → finite.Ty → Observation) (hidden : List Nat) :
    readout hidden ((lowerTerm pool finite input rows term member).eval finite
        (observe finite (graph finite.Row) depth)) =
      readout hidden ((evaluate finite input rows term).eval finite
        (observe finite (graph finite.Row) depth)) :=
  congrArg (readout hidden) (lowerTerm_observe_exact pool finite input rows term member depth)

/-- Constructor equations retain the full source image of a default at the
same depth and decrease depth only for its fallback payload. -/
theorem recordDefault_observe_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (label : Nat) (source fallback : TyTerm (Fin m))
    (member : .recordDefault label source fallback ∈ pool.terms) (depth : Nat) :
    (lowerTerm pool finite input rows (.recordDefault label source fallback) member).eval finite
        (observe finite (graph finite.Row) depth) =
      finite.recordDefault label
        ((evaluate finite input rows source).eval finite (observe finite (graph finite.Row) depth))
        (observe finite (graph finite.Row) depth (.node (evaluate finite input rows fallback))) :=
  lowerTerm_observe_exact pool finite input rows _ member depth

theorem required_observe_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (label : Nat) (payload : TyTerm (Fin m))
    (member : .required label payload ∈ pool.terms) (depth : Nat) :
    (lowerTerm pool finite input rows (.required label payload) member).eval finite
        (observe finite (graph finite.Row) depth) =
      finite.required label
        (observe finite (graph finite.Row) depth (.node (evaluate finite input rows payload))) :=
  lowerTerm_observe_exact pool finite input rows _ member depth

theorem exactEmpty_observe_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (member : .exactEmpty ∈ pool.terms) (depth : Nat) :
    (lowerTerm pool finite input rows .exactEmpty member).eval finite
        (observe finite (graph finite.Row) depth) = finite.exactEmpty := by
  have same := lowerTerm_observe_exact pool finite input rows .exactEmpty member depth
  exact same

/-- Full subtype comparisons are preserved and reflected with no algebraic
law imposed on the finite model's order. -/
theorem lowerTerm_subtype_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (first last : TyTerm (Fin m))
    (firstMember : first ∈ pool.terms) (lastMember : last ∈ pool.terms) :
    (model finite).subTy (lowerTerm pool finite input rows first firstMember)
        (lowerTerm pool finite input rows last lastMember) ↔
      (model finite).subTy (evaluate finite input rows first) (evaluate finite input rows last) := by
  change (∀ depth, finite.subTy _ _) ↔ (∀ depth, finite.subTy _ _)
  apply forall_congr'
  intro depth
  rw [lowerTerm_observe_exact pool finite input rows first firstMember depth,
    lowerTerm_observe_exact pool finite input rows last lastMember depth]

theorem lower_input_observe_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (index : Fin m) (depth : Nat) :
    (lowerValue pool finite input rows (pool.input index)).eval finite
        (observe finite (graph finite.Row) depth) =
      (input index).eval finite (observe finite (graph finite.Row) depth) := by
  have same := lowerTerm_observe_exact pool finite input rows (.var index) (pool.variables index) depth
  exact same

/-! ## Actual finite value/row constraints -/

structure Problem (inputs : Nat) where
  types : List (TyTerm (Fin inputs) × TyTerm (Fin inputs))
  rows : List (RowTerm (Fin inputs) × RowTerm (Fin inputs))

def Problem.roots (problem : Problem m) : List (TyTerm (Fin m)) :=
  problem.types.flatMap fun edge => [edge.1, edge.2]

def Problem.pool (problem : Problem m) : Pool m := collect problem.roots

theorem Problem.covers (problem : Problem m) (edge : TyTerm (Fin m) × TyTerm (Fin m))
    (member : edge ∈ problem.types) : edge.1 ∈ problem.pool.terms ∧ edge.2 ∈ problem.pool.terms := by
  constructor <;> apply collect_covers <;> apply List.mem_flatMap.mpr
  · exact ⟨edge, member, by simp⟩
  · exact ⟨edge, member, by simp⟩

def Problem.edges (problem : Problem m) : List (Fin problem.pool.size × Fin problem.pool.size) :=
  problem.types.attach.map fun edge =>
    (problem.pool.reference edge.val.1 (problem.covers edge.val edge.property).1,
      problem.pool.reference edge.val.2 (problem.covers edge.val edge.property).2)

def Problem.RowHolds (problem : Problem m) (finite : Model.{u, v}) (rows : Fin m → finite.Row) : Prop :=
  ∀ edge ∈ problem.rows, finite.subRow (rowEval finite rows edge.1) (rowEval finite rows edge.2)

def Problem.Holds (problem : Problem m) (finite : Model.{u, v})
    (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row) : Prop :=
  (∀ edge ∈ problem.types, (model finite).subTy
    (evaluate finite input rows edge.1) (evaluate finite input rows edge.2)) ∧ problem.RowHolds finite rows

def Problem.LoweredHolds (problem : Problem m) (finite : Model.{u, v})
    (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row) : Prop :=
  (∀ edge ∈ problem.edges, (model finite).subTy
    (lowerValue problem.pool finite input rows edge.1) (lowerValue problem.pool finite input rows edge.2)) ∧
      problem.RowHolds finite rows

/-- Every finite presence value/row problem has exactly the same solutions
after the actual finite lowering, for every original parameter assignment.
No compatibility law, success or solvability premise is needed. -/
theorem compile_constraints_exact (problem : Problem m) (finite : Model.{u, v})
    (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row) :
    problem.LoweredHolds finite input rows ↔ problem.Holds finite input rows := by
  apply and_congr_left
  intro _
  constructor
  · intro held edge member
    have chosen := held _ (List.mem_map.mpr ⟨⟨edge, member⟩, by simp, rfl⟩)
    exact (lowerTerm_subtype_exact problem.pool finite input rows edge.1 edge.2
      (problem.covers edge member).1 (problem.covers edge member).2).mp chosen
  · intro held edge member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    exact (lowerTerm_subtype_exact problem.pool finite input rows original.val.1 original.val.2
      (problem.covers original.val original.property).1
      (problem.covers original.val original.property).2).mpr (held original.val original.property)

/-- The row terms are the actual presence-generator row terms, and their
comparison coincides with the independent extended-model interpretation. -/
theorem row_constraints_exact (problem : Problem m) (finite : Model.{u, v})
    (input : Fin m → Ty finite.Row) (rows : Fin m → finite.Row) :
    problem.RowHolds finite rows ↔
      ∀ edge ∈ problem.rows, (model finite).subRow
        (edge.1.eval (model finite) (fun index => (input index, rows index)))
        (edge.2.eval (model finite) (fun index => (input index, rows index))) := by
  simp only [Problem.RowHolds, rowEval_exact finite input rows, model]

theorem lower_input_subtype_exact (pool : Pool m) (finite : Model.{u, v}) (input : Fin m → Ty finite.Row)
    (rows : Fin m → finite.Row) (index : Fin m) (target : Ty finite.Row) :
    (model finite).subTy (lowerValue pool finite input rows (pool.input index)) target ↔
      (model finite).subTy (input index) target := by
  change (∀ depth, finite.subTy _ _) ↔ (∀ depth, finite.subTy _ _)
  apply forall_congr'
  intro depth
  rw [lower_input_observe_exact pool finite input rows index depth]

/-- All target instances are preserved by finite-block lowering. The
existential input assignments still satisfy the original constraints;
this is not a free-parameter solved-scheme theorem. -/
theorem compile_instances_exact (problem : Problem m) (finite : Model.{u, v})
    (output : Fin m) (target : Comp (model finite)) :
    (∃ input : Fin m → Ty finite.Row, ∃ rows : Fin m → finite.Row,
      problem.LoweredHolds finite input rows ∧
      Core.PresenceGeneration.Comp.le (model finite)
        (lowerValue problem.pool finite input rows (problem.pool.input output), rows output) target) ↔
    (∃ input : Fin m → Ty finite.Row, ∃ rows : Fin m → finite.Row,
      problem.Holds finite input rows ∧
      Core.PresenceGeneration.Comp.le (model finite) (input output, rows output) target) := by
  apply exists_congr
  intro input
  apply exists_congr
  intro rows
  exact and_congr (compile_constraints_exact problem finite input rows)
    (and_congr (lower_input_subtype_exact problem.pool finite input rows output target.1) Iff.rfl)

end Yulang.PresenceOpenTailGenerationLowering
