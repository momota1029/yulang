import Yulang.CommonEffectScopedCompilation
import Yulang.CommonEffectPolarity

/-! Exact compilation of actual finite source type inequalities while all
captured types and all rows are fixed. This exposes a finite residual after
relative clamping. It does NOT turn residuals into restrictions on otherwise
free parameters of a purported returned solution scheme. -/
namespace Yulang.CommonEffectCapturedCompilation
open Common (Ty Row Equivalent)
open Core.PresenceGeneration (TyTerm)
open CommonEffectRequestGeneration (Computation)
open CommonEffectScopedClamping (Index input fixed)
open CommonEffectScopedCompilation (Names InputMatches inputValue rows)
open PresenceOpenTailGenerationLowering (Pool)

variable {flex captured scopes : Nat}

theorem frozen_good (term : TyTerm α) (positive : Bool) :
    CommonEffectPolarity.goodType (fun _ => none) positive term = true := by
  induction term generalizing positive <;> cases positive <;> simp_all [CommonEffectPolarity.goodType]

theorem term_congr (term : TyTerm α) (first last : α → Computation)
    (sameRows : ∀ name, (first name).2 = (last name).2)
    (sameValues : ∀ name, Equivalent (first name).1 (last name).1) :
    Equivalent (term.eval Common.model first) (term.eval Common.model last) :=
  ⟨CommonEffectPolarity.type_ordered term (fun _ => none) first last ⟨sameRows, sameValues⟩ true (frozen_good term true),
    CommonEffectPolarity.type_ordered term (fun _ => none) first last ⟨sameRows, sameValues⟩ false (frozen_good term false)⟩

theorem typeHolds_congr (problem : CommonPresenceConstraintGraph.Problem inputs) (rowValues : Fin inputs → Row)
    (first last : Fin inputs → Ty) (same : ∀ name, Equivalent (first name) (last name)) :
    CommonPresenceConstraintGraph.TypeHolds problem rowValues first ↔
      CommonPresenceConstraintGraph.TypeHolds problem rowValues last := by
  constructor
  · intro accepted edge member
    have source := term_congr edge.1 (fun name => (first name, rowValues name))
      (fun name => (last name, rowValues name)) (fun _ => rfl) same
    have target := term_congr edge.2 (fun name => (first name, rowValues name))
      (fun name => (last name, rowValues name)) (fun _ => rfl) same
    exact Common.subtype_trans source.2 (Common.subtype_trans (accepted edge member) target.1)
  · intro accepted edge member
    have source := term_congr edge.1 (fun name => (first name, rowValues name))
      (fun name => (last name, rowValues name)) (fun _ => rfl) same
    have target := term_congr edge.2 (fun name => (first name, rowValues name))
      (fun name => (last name, rowValues name)) (fun _ => rfl) same
    exact Common.subtype_trans source.1 (Common.subtype_trans (accepted edge member) target.2)

def mixedValues (assignment : Names flex captured → Computation) (flexible : Fin flex → Ty) :
    Names flex captured → Ty :=
  Fin.addCases flexible (fun index => (assignment (Fin.natAdd flex index)).1)

def compile (problem : CommonPresenceConstraintGraph.Problem (flex + captured)) :
    CommonEffectScopedClamping.Problem flex problem.pool.size 0 scopes (Names flex captured) :=
  CommonEffectScopedCompilation.compile problem.pool problem.edges

theorem compile_reflects (problem : CommonPresenceConstraintGraph.Problem (flex + captured))
    (assignment : Names flex captured → Computation) (values : Index flex problem.pool.size → Ty)
    (model : (compile (scopes := scopes) problem).OriginalModels assignment values) :
    CommonPresenceConstraintGraph.TypeHolds problem (rows assignment) (inputValue assignment values) := by
  obtain ⟨realizes, agree, edges⟩ := (CommonEffectScopedCompilation.compile_models problem.pool problem.edges assignment values).mp model
  have accepted := (CommonPresenceConstraintGraph.compiled_edges_exact problem (rows assignment) (values ∘ fixed) realizes).mp edges
  exact (typeHolds_congr problem (rows assignment) (inputValue assignment values)
    (CommonPresenceConstraintGraph.restrict problem.pool (values ∘ fixed)) agree).mpr accepted

def extendNodes (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (flexible : Fin flex → Ty) : Index flex pool.size → Ty :=
  Fin.addCases flexible (CommonPresenceConstraintGraph.extend pool (rows assignment) (mixedValues assignment flexible))

@[simp] theorem extendNodes_input (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (flexible : Fin flex → Ty) (index : Fin flex) :
    extendNodes pool assignment flexible (input index) = flexible index := by
  simp only [extendNodes, input, Fin.addCases_left]

@[simp] theorem extendNodes_fixed (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (flexible : Fin flex → Ty) (index : Fin pool.size) :
    extendNodes pool assignment flexible (fixed index) =
      CommonPresenceConstraintGraph.extend pool (rows assignment) (mixedValues assignment flexible) index := by
  simp only [extendNodes, fixed, Fin.addCases_right]

theorem inputValue_extend (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (flexible : Fin flex → Ty) :
    inputValue assignment (extendNodes pool assignment flexible) = mixedValues assignment flexible := by
  funext name
  refine Fin.addCases (fun index => ?_) (fun index => ?_) name
  all_goals simp only [inputValue, mixedValues, Common.model, Fin.addCases_left, Fin.addCases_right, extendNodes_input]

theorem extend_inputs (pool : Pool (flex + captured)) (assignment : Names flex captured → Computation)
    (flexible : Fin flex → Ty) : InputMatches pool assignment (extendNodes pool assignment flexible) := by
  intro name
  rw [inputValue_extend, extendNodes_fixed]
  change Equivalent _ (CommonPresenceConstraintGraph.restrict pool
    (CommonPresenceConstraintGraph.extend pool (rows assignment) (mixedValues assignment flexible)) name)
  rw [CommonPresenceConstraintGraph.restrict_extend]
  exact Common.equivalent_refl _

theorem compile_extends (problem : CommonPresenceConstraintGraph.Problem (flex + captured))
    (assignment : Names flex captured → Computation) (flexible : Fin flex → Ty)
    (accepted : CommonPresenceConstraintGraph.TypeHolds problem (rows assignment) (mixedValues assignment flexible)) :
    (compile (scopes := scopes) problem).OriginalModels assignment (extendNodes problem.pool assignment flexible) := by
  have tail : extendNodes problem.pool assignment flexible ∘ fixed =
      CommonPresenceConstraintGraph.extend problem.pool (rows assignment) (mixedValues assignment flexible) := by
    funext index
    exact extendNodes_fixed problem.pool assignment flexible index
  apply (CommonEffectScopedCompilation.compile_models problem.pool problem.edges assignment _).mpr
  refine ⟨?_, extend_inputs problem.pool assignment flexible, ?_⟩
  · rw [tail]
    exact CommonPresenceConstraintGraph.extend_realizes _ _ _
  · rw [tail]
    apply (CommonPresenceConstraintGraph.compiled_edges_exact problem (rows assignment) _
      (CommonPresenceConstraintGraph.extend_realizes _ _ _)).mpr
    simpa only [CommonPresenceConstraintGraph.restrict_extend] using accepted

/-- Arbitrary independent rows and captures are fixed before flexible type
witnesses. No child/width/row grammar restriction is introduced. -/
theorem source_models_exact (problem : CommonPresenceConstraintGraph.Problem (flex + captured))
    (assignment : Names flex captured → Computation) :
    (∃ flexible : Fin flex → Ty,
      CommonPresenceConstraintGraph.TypeHolds problem (rows assignment) (mixedValues assignment flexible)) ↔
    ∃ values : Index flex problem.pool.size → Ty, (compile (scopes := scopes) problem).OriginalModels assignment values := by
  constructor
  · rintro ⟨flexible, accepted⟩
    exact ⟨extendNodes problem.pool assignment flexible, compile_extends problem assignment flexible accepted⟩
  · rintro ⟨values, model⟩
    refine ⟨values ∘ input, ?_⟩
    exact compile_reflects problem assignment values model

/-- Exact finite relative clamping of actual source inequalities. The
residual remains explicit, so this is not an unrestricted output scheme. -/
theorem source_clamped_exact (problem : CommonPresenceConstraintGraph.Problem (flex + captured))
    (assignment : Names flex captured → Computation) :
    (∃ flexible : Fin flex → Ty,
      CommonPresenceConstraintGraph.TypeHolds problem (rows assignment) (mixedValues assignment flexible)) ↔
    ∃ values : Index flex problem.pool.size → Ty, ∃ parameters : Fin flex → Ty,
      CommonPresenceTailRegular.Models ((compile (scopes := scopes) problem).clamped assignment parameters) values ∧
      (compile (scopes := scopes) problem).residualFormula.Holds (fun index => (values index, Common.rowEmpty)) := by
  rw [source_models_exact (scopes := scopes)]
  apply exists_congr
  intro values
  exact (CommonEffectScopedClamping.factor_exact (compile problem) assignment values).trans
    (exists_congr fun parameters => and_congr_right fun _ =>
      (CommonEffectScopedClamping.residualFormula_exact (compile problem) values (fun _ => Common.rowEmpty)).symm)

end Yulang.CommonEffectCapturedCompilation
