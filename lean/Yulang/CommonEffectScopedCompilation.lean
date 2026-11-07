import Yulang.CommonEffectScopedClamping

/-! Actual finite type syntax compiled with an explicit flexible/captured
partition. All original collected value nodes remain as trailing nodes.
Original flexible variables additionally have leading clamped slots; their
duplicate collected nodes are equations, not fresh captures. Rows retain
their original identifiers. This bridge emits residual comparisons and does
not assert that the residuals or rigid universal binders have been solved. -/
namespace Yulang.CommonEffectScopedCompilation
open Common (Ty Row Equivalent)
open Core.PresenceGeneration (TyTerm)
open CommonEffectRequestGeneration (Computation RowExpr)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonEffectScopedRegular (Body)
open CommonEffectScopedClamping (Index input fixed)

variable {flex captured scopes : Nat}

abbrev Names (flex captured : Nat) := Fin (flex + captured)

def inputValue (assignment : Names flex captured → Computation)
    (values : Index flex rigid → Ty) : Names flex captured → Ty :=
  Fin.addCases (fun index => values (input index))
    (fun index => (assignment (Fin.natAdd flex index)).1)

def rows (assignment : Names flex captured → Computation) : Names flex captured → Row :=
  fun name => (assignment name).2

def InputMatches (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (values : Index flex pool.size → Ty) : Prop :=
  ∀ name, Equivalent (inputValue assignment values name) (values (fixed (pool.input name)))

def lowerNode (pool : Pool (flex + captured)) (term : TyTerm (Names flex captured))
    (member : term ∈ pool.terms) : Body (flex + pool.size) 0 scopes (Names flex captured) :=
  match term with
  | .var name => Fin.addCases (fun index => .ref (input index))
      (fun index => .constant (.var (Fin.natAdd flex index))) name
  | .base scalar => .atom (.base scalar)
  | .bottom => .atom .bottom
  | .top => .atom .top
  | .union first last =>
      .union (.ref (fixed (pool.child _ member first (by simp [subterms]))))
        (.ref (fixed (pool.child _ member last (by simp [subterms]))))
  | .inter first last =>
      .inter (.ref (fixed (pool.child _ member first (by simp [subterms]))))
        (.ref (fixed (pool.child _ member last (by simp [subterms]))))
  | .pair first last => .atom (.pair
      (.inl (fixed (pool.child _ member first (by simp [subterms]))))
      (.inl (fixed (pool.child _ member last (by simp [subterms])))))
  | .emptyRecord => .atom .emptyRecord
  | .exactEmpty => .atom .exactEmpty
  | .required label payload =>
      .record label (.inl (fixed (pool.child _ member payload (by simp [subterms])))) (.atom .emptyRecord)
  | .record label payload tail =>
      .record label (.inl (fixed (pool.child _ member payload (by simp [subterms]))))
        (.ref (fixed (pool.child _ member tail (by simp [subterms]))))
  | .recordDefault label source fallback =>
      .recordDefault label (.ref (fixed (pool.child _ member source (by simp [subterms]))))
        (.inl (fixed (pool.child _ member fallback (by simp [subterms]))))
  | .variant label payload => .atom (.variant label
      (.inl (fixed (pool.child _ member payload (by simp [subterms])))))
  | .arrow arg incoming result outgoing => .atom (.arrow
      (.inl (fixed (pool.child _ member arg (by simp [subterms])))) (RowExpr.fromPresence incoming)
      (.inl (fixed (pool.child _ member result (by simp [subterms])))) (RowExpr.fromPresence outgoing))

def bodies (pool : Pool (flex + captured)) :
    Fin pool.size → Body (flex + pool.size) 0 scopes (Names flex captured) :=
  fun index => lowerNode pool (pool.termAt index) (pool.at_mem index)

theorem variable_value (pool : Pool (flex + captured)) (name : Names flex captured)
    (assignment : Names flex captured → Computation) (values : Index flex pool.size → Ty) :
    (lowerNode (scopes := scopes) pool (.var name) (pool.variables name)).value assignment values =
      inputValue assignment values name := by
  refine Fin.addCases (fun index => ?_) (fun index => ?_) name
  all_goals simp only [lowerNode, inputValue, Common.model, Fin.addCases_left, Fin.addCases_right, Body.value, TyTerm.eval]

theorem lowerNode_exact (pool : Pool (flex + captured)) (term : TyTerm (Names flex captured))
    (member : term ∈ pool.terms) (assignment : Names flex captured → Computation)
    (values : Index flex pool.size → Ty) (agree : InputMatches pool assignment values) :
    Equivalent ((lowerNode (scopes := scopes) pool term member).value assignment values)
      ((CommonPresenceConstraintGraph.lowerNode pool term member).eval (rows assignment) (values ∘ fixed)) := by
  cases term
  case var name =>
    rw [variable_value]
    exact agree name
  case arrow arg incoming result outgoing =>
    simp only [lowerNode, Body.value, CommonEffectScopedRegular.layerValue,
      CommonEffectScopedRegular.refValue, RowExpr.eval_fromPresence,
      CommonPresenceConstraintGraph.lowerNode, CommonRowTailInference.Body.eval,
      CommonRowTailInference.layerAtRows, CommonPresenceTailLayers.quoteLayer,
      CommonSyntax.Layer.map, Function.comp_apply]
    have rowSame (row : Core.PresenceGeneration.RowTerm (Names flex captured)) :
        RowFlowSchemes.eval Common.rowAlgebra (rows assignment) (PresenceSourceConstraintSupport.originalRow row) =
          row.eval Common.model assignment := by
      induction row <;> simp_all only [PresenceSourceConstraintSupport.originalRow,
        RowFlowSchemes.eval, Core.PresenceGeneration.RowTerm.eval, Common.rowAlgebra, Common.model, rows]
    rw [rowSame incoming, rowSame outgoing]
    exact Common.equivalent_refl _
  all_goals exact Common.equivalent_refl _

def Equations (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (values : Index flex pool.size → Ty) : Prop :=
  ∀ index, Equivalent ((bodies (scopes := scopes) pool index).value assignment values) (values (fixed index))

theorem equations_inputs (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (values : Index flex pool.size → Ty) (equations : Equations (scopes := scopes) pool assignment values) :
    InputMatches pool assignment values := by
  intro name
  have node := equations (pool.input name)
  simpa only [bodies, Pool.input, Pool.termAt_reference, variable_value] using node

theorem equations_exact (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (values : Index flex pool.size → Ty) :
    Equations (scopes := scopes) pool assignment values ↔
      CommonPresenceConstraintGraph.Realizes pool (rows assignment) (values ∘ fixed) ∧ InputMatches pool assignment values := by
  constructor
  · intro equations
    have agree := equations_inputs pool assignment values equations
    refine ⟨?_, agree⟩
    intro index
    exact Common.equivalent_trans
      (Common.equivalent_symm (lowerNode_exact pool _ _ assignment values agree)) (equations index)
  · rintro ⟨realizes, agree⟩ index
    exact Common.equivalent_trans (lowerNode_exact pool _ _ assignment values agree) (realizes index)

/-- Only endpoints which really are flexible variable syntax are clamped.
Every constructor/captured endpoint remains its original trailing node. -/
def endpoint (pool : Pool (flex + captured)) (index : Fin pool.size) : Index flex pool.size :=
  match pool.termAt index with
  | .var name => Fin.addCases input (fun _ => fixed index) name
  | _ => fixed index

theorem endpoint_exact (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (values : Index flex pool.size → Ty) (agree : InputMatches pool assignment values) (index : Fin pool.size) :
    Equivalent (values (endpoint pool index)) (values (fixed index)) := by
  unfold endpoint
  split
  next name same =>
    have reference := pool.reference_termAt index
    have nameIndex : pool.input name = index := by simpa only [same, Pool.input] using reference
    rw [← nameIndex]
    have relevant := agree name
    change Equivalent (Fin.addCases (fun i => values (input i))
      (fun i => (assignment (Fin.natAdd flex i)).1) name) _ at relevant
    revert relevant
    refine Fin.addCases (fun name => ?_) (fun name => ?_) name
    · simp only [Common.model, Fin.addCases_left]
      exact id
    · simp only [Common.model, Fin.addCases_right]
      intro _
      exact Common.equivalent_refl _
  next => exact Common.equivalent_refl _

def compile (pool : Pool (flex + captured)) (edges : List (Fin pool.size × Fin pool.size)) :
    CommonEffectScopedClamping.Problem flex pool.size 0 scopes (Names flex captured) where
  bodies := bodies pool
  edges := edges.map (fun edge => (endpoint pool edge.1, endpoint pool edge.2))

theorem edges_exact (pool : Pool (flex + captured)) (edges : List (Fin pool.size × Fin pool.size))
    (assignment : Names flex captured → Computation) (values : Index flex pool.size → Ty)
    (agree : InputMatches pool assignment values) :
    CommonPresenceConstraintGraph.EdgesHold (compile (scopes := scopes) pool edges).edges values ↔
      CommonPresenceConstraintGraph.EdgesHold edges (values ∘ fixed) := by
  simp only [compile, CommonPresenceConstraintGraph.EdgesHold, List.forall_mem_map]
  constructor
  · intro accepted edge member
    exact Common.subtype_trans (endpoint_exact pool assignment values agree edge.1).2
      (Common.subtype_trans (accepted edge member) (endpoint_exact pool assignment values agree edge.2).1)
  · intro accepted edge member
    exact Common.subtype_trans (endpoint_exact pool assignment values agree edge.1).1
      (Common.subtype_trans (accepted edge member) (endpoint_exact pool assignment values agree edge.2).2)

theorem compile_models (pool : Pool (flex + captured)) (edges : List (Fin pool.size × Fin pool.size))
    (assignment : Names flex captured → Computation) (values : Index flex pool.size → Ty) :
    (compile (scopes := scopes) pool edges).OriginalModels assignment values ↔
      CommonPresenceConstraintGraph.Realizes pool (rows assignment) (values ∘ fixed) ∧
      InputMatches pool assignment values ∧
      CommonPresenceConstraintGraph.EdgesHold edges (values ∘ fixed) := by
  change Equations pool assignment values ∧ _ ↔ _
  rw [equations_exact]
  constructor
  · rintro ⟨⟨realizes, agree⟩, edgesHold⟩
    exact ⟨realizes, agree, (edges_exact pool edges assignment values agree).mp edgesHold⟩
  · rintro ⟨realizes, agree, edgesHold⟩
    exact ⟨⟨realizes, agree⟩, (edges_exact pool edges assignment values agree).mpr edgesHold⟩

end Yulang.CommonEffectScopedCompilation
