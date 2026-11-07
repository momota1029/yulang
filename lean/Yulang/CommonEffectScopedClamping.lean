import Yulang.CommonEffectScopedRegular
import Yulang.CommonPresenceConstraintGraph

/-! Relative clamping with a syntactic flexible/rigid partition. Captures and
rigid type leaves are never substituted or clamped. Only the leading flexible
unknowns are replaced by bound-family equations. Residual rigid comparisons
are emitted explicitly as finite Formula syntax; they are NOT claimed solved
or moved into conditions on parameters of a returned solved scheme. -/
namespace Yulang.CommonEffectScopedClamping
open Common (Ty Row Equivalent Subtype)
open CommonEffectRequestGeneration (Computation)
open CommonEffectFormula (Formula)
open CommonEffectScopedRegular (Body)
open LayerBoundTemplates (Constraint lowerBounds upperBounds ancestors)
open CommonBoundCoalescing (Models Consistent expand)

variable {flex rigid labels scopes : Nat}

abbrev Index (flex rigid : Nat) := Fin (flex + rigid)
abbrev Template (flex rigid : Nat) := LayerBoundTemplates.Problem flex (Index flex rigid)
abbrev CompiledBody (flex rigid labels : Nat) := CommonPresenceTailLayers.Body (flex + rigid) labels (CommonPresenceTailRegular.Payload (flex + rigid))

def input (index : Fin flex) : Index flex rigid := Fin.castAdd rigid index
def fixed (index : Fin rigid) : Index flex rigid := Fin.natAdd flex index

def owner : Index flex rigid → Option (Fin flex) := Fin.addCases some (fun _ => none)

def edgeConstraint (edge : Index flex rigid × Index flex rigid) : Constraint flex (Index flex rigid) :=
  match owner edge.1, owner edge.2 with
  | some source, some target => .flow source target
  | some source, none => .upper source edge.2
  | none, some target => .lower edge.1 target
  | none, none => .check edge.1 edge.2

theorem edgeConstraint_exact (edge : Index flex rigid × Index flex rigid) (values : Index flex rigid → Ty) :
    CommonBoundCoalescing.Holds values (values ∘ input) (edgeConstraint edge) ↔ Subtype (values edge.1) (values edge.2) := by
  rcases edge with ⟨source, target⟩
  refine Fin.addCases (fun source => ?_) (fun source => ?_) source
  all_goals refine Fin.addCases (fun target => ?_) (fun target => ?_) target
  all_goals simp only [edgeConstraint, owner, Fin.addCases_left, Fin.addCases_right,
    CommonBoundCoalescing.Holds, Function.comp_apply, input]

def template (edges : List (Index flex rigid × Index flex rigid)) : Template flex rigid := edges.map edgeConstraint

theorem template_exact (edges : List (Index flex rigid × Index flex rigid)) (values : Index flex rigid → Ty) :
    Models values (template edges) (values ∘ input) ↔ CommonPresenceConstraintGraph.EdgesHold edges values := by
  simp only [Models, template, List.forall_mem_map, edgeConstraint_exact, CommonPresenceConstraintGraph.EdgesHold]

def quote (body : CompiledBody flex rigid labels) (values : Index flex rigid → Ty) : Ty :=
  (body.quote (CommonPresenceTailRegular.payload values)).eval values

def joinRefs : List (Index flex rigid) → CompiledBody flex rigid labels
  | [] => .atom .bottom
  | index :: rest => .union (.ref index) (joinRefs rest)

def meetRefs : List (Index flex rigid) → CompiledBody flex rigid labels
  | [] => .atom .top
  | index :: rest => .inter (.ref index) (meetRefs rest)

def joinBodies : List (CompiledBody flex rigid labels) → CompiledBody flex rigid labels
  | [] => .atom .bottom
  | body :: rest => .union body (joinBodies rest)

theorem joinRefs_quote (indices : List (Index flex rigid)) (values : Index flex rigid → Ty) :
    quote (joinRefs (labels := labels) indices) values = CommonBoundCoalescing.joinTypes (indices.map values) := by
  induction indices with
  | nil => rfl
  | cons index rest ih => exact congrArg (CommonSyntax.Layer.union (values index)) ih

theorem meetRefs_quote (indices : List (Index flex rigid)) (values : Index flex rigid → Ty) :
    quote (meetRefs (labels := labels) indices) values = CommonBoundCoalescing.meetTypes (indices.map values) := by
  induction indices with
  | nil => rfl
  | cons index rest ih => exact congrArg (CommonSyntax.Layer.inter (values index)) ih

theorem joinBodies_quote (bodies : List (CompiledBody flex rigid labels)) (values : Index flex rigid → Ty) :
    quote (joinBodies bodies) values = CommonBoundCoalescing.joinTypes (bodies.map (fun body => quote body values)) := by
  induction bodies with
  | nil => rfl
  | cons body rest ih => exact congrArg (CommonSyntax.Layer.union (quote body values)) ih

theorem joinTypes_congr (indices : List β) (first last : β → Ty)
    (same : ∀ index ∈ indices, Equivalent (first index) (last index)) :
    Equivalent (CommonBoundCoalescing.joinTypes (indices.map first)) (CommonBoundCoalescing.joinTypes (indices.map last)) := by
  induction indices with
  | nil => exact Common.equivalent_refl _
  | cons index rest ih =>
    have head := same index (by simp)
    have tail := ih (fun index member => same index (List.mem_cons_of_mem _ member))
    exact ⟨Common.common_union_mono head.1 tail.1, Common.common_union_mono head.2 tail.2⟩

def boundBody (problem : Template flex rigid) (parameters : Fin flex → Ty) (target : Fin flex) : CompiledBody flex rigid labels :=
  .union (joinRefs (lowerBounds problem target))
    (joinBodies ((ancestors problem target).map (fun source =>
      .inter (.atom ((parameters source).map Sum.inr)) (meetRefs (upperBounds problem source)))))

theorem boundBody_exact (problem : Template flex rigid) (parameters : Fin flex → Ty)
    (values : Index flex rigid → Ty) (target : Fin flex) :
    Equivalent (quote (boundBody (labels := labels) problem parameters target) values) (expand values problem parameters target) := by
  change Equivalent
    (.union (quote (joinRefs (lowerBounds problem target)) values)
      (quote (joinBodies ((ancestors problem target).map (fun source =>
        .inter (.atom ((parameters source).map Sum.inr)) (meetRefs (upperBounds problem source))))) values))
    (.union (CommonBoundCoalescing.lower values problem target) (CommonBoundCoalescing.variablePart values problem parameters target))
  have lowerSame := joinRefs_quote (labels := labels) (lowerBounds problem target) values
  have parts := joinBodies_quote (labels := labels)
    ((ancestors problem target).map (fun source =>
      .inter (.atom ((parameters source).map Sum.inr)) (meetRefs (upperBounds problem source)))) values
  rw [lowerSame, parts]
  have parameterSame : Equivalent
      (CommonBoundCoalescing.joinTypes (((ancestors problem target).map (fun source =>
        (.inter (.atom ((parameters source).map Sum.inr)) (meetRefs (upperBounds problem source)) : CompiledBody flex rigid labels))).map
          (fun body => quote body values)))
      (CommonBoundCoalescing.variablePart values problem parameters target) := by
    rw [List.map_map]
    apply joinTypes_congr
    intro source _
    change Equivalent
      (.inter (CommonPresenceTailLayers.quoteLayer (CommonPresenceTailRegular.payload values) ((parameters source).map Sum.inr))
        (quote (meetRefs (upperBounds problem source)) values))
      (.inter (parameters source) (CommonBoundCoalescing.upper values problem source))
    have constantSame := CommonEffectScopedRegular.quote_external (parameters source) values
    have upperSame := meetRefs_quote (labels := labels) (upperBounds problem source) values
    rw [upperSame]
    exact ⟨Common.common_inter_mono constantSame.1 (Common.subtype_refl _),
      Common.common_inter_mono constantSame.2 (Common.subtype_refl _)⟩
  exact ⟨Common.common_union_mono (Common.subtype_refl _) parameterSame.1,
    Common.common_union_mono (Common.subtype_refl _) parameterSame.2⟩

structure Problem (flex rigid labels scopes : Nat) (α : Type) where
  bodies : Fin rigid → Body (flex + rigid) labels scopes α
  edges : List (Index flex rigid × Index flex rigid)

def Problem.OriginalModels (problem : Problem flex rigid labels scopes α) (assignment : α → Computation) (values : Index flex rigid → Ty) : Prop :=
  (∀ index, Equivalent ((problem.bodies index).value assignment values) (values (fixed index))) ∧
    CommonPresenceConstraintGraph.EdgesHold problem.edges values

def Problem.clamped (problem : Problem flex rigid labels scopes α) (assignment : α → Computation) (parameters : Fin flex → Ty) :
    CommonPresenceTailRegular.Graph (flex + rigid) labels :=
  Fin.addCases (fun index => boundBody (template problem.edges) parameters index)
    (fun index => (problem.bodies index).compile assignment)

def Problem.Residual (problem : Problem flex rigid labels scopes α) (values : Index flex rigid → Ty) : Prop :=
  Consistent values (template problem.edges)

def Problem.residualFormula (problem : Problem flex rigid labels scopes α) : Formula scopes (Index flex rigid) :=
  CommonEffectUniversalArms.andAll ((CommonBoundCoalescing.rigidComparisons (template problem.edges)).map
    (fun pair => .tyLe (.var pair.1) (.var pair.2)))

theorem residualFormula_exact (problem : Problem flex rigid labels scopes α) (values : Index flex rigid → Ty)
    (rows : Index flex rigid → Row) :
    problem.residualFormula.Holds (fun index => (values index, rows index)) ↔ problem.Residual values := by
  simp only [Problem.residualFormula, CommonEffectUniversalArms.andAll_exact, List.forall_mem_map,
    CommonEffectFormula.Formula.holds_tyLe, Core.PresenceGeneration.TyTerm.eval, Problem.Residual, Consistent]

theorem original_clamped_model (problem : Problem flex rigid labels scopes α) (assignment : α → Computation)
    (values : Index flex rigid → Ty) (model : problem.OriginalModels assignment values) :
    CommonPresenceTailRegular.Models (problem.clamped assignment (values ∘ input)) values ∧ problem.Residual values := by
  have flat := (template_exact problem.edges values).mpr model.2
  refine ⟨?_, (CommonBoundCoalescing.consistent_iff_satisfiable values (template problem.edges)).mpr ⟨values ∘ input, flat⟩⟩
  intro index
  refine Fin.addCases (fun index => ?_) (fun index => ?_) index
  · simp only [Problem.clamped, Fin.addCases_left]
    exact Common.equivalent_trans (boundBody_exact (template problem.edges) (values ∘ input) values index)
      (CommonBoundCoalescing.expand_retraction flat index)
  · simp only [Problem.clamped, Fin.addCases_right]
    exact Common.equivalent_trans ((problem.bodies index).compile_exact assignment values) (model.1 index)

theorem clamped_original_model (problem : Problem flex rigid labels scopes α) (assignment : α → Computation)
    (parameters : Fin flex → Ty) (values : Index flex rigid → Ty)
    (model : CommonPresenceTailRegular.Models (problem.clamped assignment parameters) values)
    (residual : problem.Residual values) : problem.OriginalModels assignment values := by
  have same (index : Fin flex) : Equivalent (expand values (template problem.edges) parameters index) (values (input index)) := by
    have equation := model (input index)
    simp only [input, Problem.clamped, Fin.addCases_left] at equation
    exact Common.equivalent_trans (Common.equivalent_symm (boundBody_exact (template problem.edges) parameters values index)) equation
  refine ⟨?_, (template_exact problem.edges values).mp ?_⟩
  · intro index
    have equation := model (fixed index)
    simp only [fixed, Problem.clamped, Fin.addCases_right] at equation
    exact Common.equivalent_trans (Common.equivalent_symm ((problem.bodies index).compile_exact assignment values)) equation
  · exact (CommonBoundCoalescing.models_congr values (template problem.edges) same).mp
      (CommonBoundCoalescing.expand_satisfies residual parameters)

/-- Exact relative factorization. The finite residual comparisons are still
part of the problem, not a condition on a purported solved output scheme. -/
theorem factor_exact (problem : Problem flex rigid labels scopes α) (assignment : α → Computation) (values : Index flex rigid → Ty) :
    problem.OriginalModels assignment values ↔
      ∃ parameters : Fin flex → Ty,
        CommonPresenceTailRegular.Models (problem.clamped assignment parameters) values ∧ problem.Residual values :=
  ⟨fun model => ⟨values ∘ input, original_clamped_model problem assignment values model⟩,
    fun ⟨parameters, model, residual⟩ => clamped_original_model problem assignment parameters values model residual⟩

theorem original_retraction (problem : Problem flex rigid labels scopes α) (assignment : α → Computation)
    (values : Index flex rigid → Ty) (model : problem.OriginalModels assignment values) :
    ∀ index, Equivalent
      (CommonPresenceTailRegular.solveBlock (problem.clamped assignment (values ∘ input)) values index) (values index) :=
  CommonPresenceTailRegular.solveBlock_retract _ values (original_clamped_model problem assignment values model).1
end Yulang.CommonEffectScopedClamping
