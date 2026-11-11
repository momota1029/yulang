import Yulang.GeneralSourceK2
import Yulang.GeneralSourceStateExamples

/-!
# Normalized source K2 regressions

The states, interval arguments, associated output and models are the original
shared-state examples. Only their separately checked observation snapshots are
new. The shadow residual is left unknown, preserving all ordinary models.
-/
namespace Yulang.GeneralSourceK2Examples

open GeneralSourceStateExamples
open GeneralNormalizedObservation
open GeneralSourceK2
open Core.PresenceGeneration (TyTerm)

abbrev indexView : Snapshot indexState where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := fun i => Fin.elim0 i
  heads := fun slot => if slot = 0 then .scalar .str else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.base .str : TyTerm (Fin 3)) = term := by
        simpa [Head.term] using recorded
      subst term
      exact .head rfl
    · simp [zero, Head.term, Deferred.term] at recorded

abbrev loopView : Snapshot loopState where
  kinds := 1
  shapes := fun _ => .record [7]
  shapes_injective := by intro i j _; apply Fin.ext; omega
  canonical := by intro i; simp [Shape.Canonical]
  heads := fun _ => .structural 0 (fun _ => 0)
  checked := by
    intro slot term recorded
    have zero : slot = 0 := by
      have bound := slot.isLt
      change slot.val < 1 at bound
      apply Fin.ext
      change slot.val = 0
      omega
    subst slot
    have same : (.record 7 (.var 0) .emptyRecord : TyTerm (Fin 1)) = term := by
      simpa [Head.term, Shape.term, recordTerm, List.ofFn_succ] using recorded
    subst term
    exact .trans (.head rfl) .required

/-- One finite unfolding exposes the duplicate field; the existing shadow
law removes it. The original residual reference survives that normalization. -/
theorem shadow_normalization :
    Rewrites shadowState (.var 0) (.record 7 (.var 1) (.var 0)) ∧
      Rewrites shadowState (.record 7 (.var 1) (.record 7 (.var 1) (.var 0)))
        (.record 7 (.var 1) (.var 0)) := by
  have unfoldHead : Rewrites shadowState (.var 0) (.record 7 (.var 1) (.var 0)) := .head rfl
  exact ⟨.trans unfoldHead (.trans (.record (.refl _) unfoldHead) .shadow), .shadow⟩

abbrev shadowView : Snapshot shadowState where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := fun i => Fin.elim0 i
  heads := fun slot => if slot = 0 then .deferred (.residual [(7, 1)] (.var 0)) else .scalar .int
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.record 7 (.var 1) (.var 0) : TyTerm (Fin 2)) = term := by
        simpa [Head.term, Deferred.term, recordTerm] using recorded
      subst term
      exact shadow_normalization.1
    · have one : slot = 1 := by
        have bound := slot.isLt
        change slot.val < 2 at bound
        have nonzero : slot.val ≠ 0 := fun h => zero (Fin.ext h)
        apply Fin.ext
        change slot.val = 1
        omega
      subst slot
      have same : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [Head.term] using recorded
      subst term
      exact .head rfl

theorem index_pending_not_rootK2 :
    GeneralSourceState.Linked indexState indexDemand ∧
      (∀ key, GeneralSourceState.Models indexState (indexModel key)) ∧
      RootPending indexView indexDemand indexNeeded ∧ ¬ RootK2 indexView indexDemand indexNeeded := by
  have linked := GeneralSourceStateExamples.index_example.1
  have pending : RootPending indexView indexDemand indexNeeded := by
    apply (pending_graph_iff indexView indexDemand linked indexNeeded).mpr
    exact ⟨⟨1, by simp [roles, indexRole]⟩, 1, Or.inr rfl, rfl, rfl⟩
  exact ⟨linked, GeneralSourceStateExamples.index_example.2.1, pending,
    pending_excludes_rootK2 indexView indexDemand indexNeeded pending⟩

theorem loop_rootK2 :
    GeneralSourceState.Linked loopState loopDemand ∧
      GeneralSourceState.Models loopState loopModel ∧
      RootK2 loopView loopDemand loopNeeded ∧ ¬ RootPending loopView loopDemand loopNeeded ∧
      RecursAt loopView 0 := by
  have linked := GeneralSourceStateExamples.recursive_example.1
  have closed : ∀ slot, loopView.graph slot ≠ .unresolved := by
    intro slot
    simp [Snapshot.graph, Head.node]
  have ready : ¬ RootPending loopView loopDemand loopNeeded := by
    rintro ⟨argument, _, unknown⟩
    exact unknown ⟨0, rfl, closed 0⟩
  have recursive : GeneralSourceBoundary.GraphK2 loopView.graph 0 := by
    apply Or.inl
    refine ⟨0, [0], ?_, 0, by simp, .nil _⟩
    simp [Snapshot.graph, Head.node, Shape.arity, List.ofFn_succ]
  have inspected : ¬ RootInspectionUnknown loopView loopDemand := by
    rintro ⟨_, node, _, incomplete⟩
    exact incomplete (fun child _ => closed child)
  exact ⟨linked, GeneralSourceStateExamples.recursive_example.2.1,
    ⟨linked, ready, inspected, ⟨0, by simp [roles, unaryRole]⟩, 0, rfl, fun node _ => closed node, recursive⟩,
    ready, graphK2_sound loopView 0 recursive⟩

theorem shadow_not_rootK2 :
    GeneralSourceState.Linked shadowState loopDemand ∧
      GeneralSourceState.Models shadowState shadowModel ∧
      RootPending shadowView loopDemand loopNeeded ∧ ¬ RootK2 shadowView loopDemand loopNeeded ∧
      ¬ GeneralSourceBoundary.GraphK2 shadowView.graph 0 ∧
      (shadowModel 0).1 = Common.required 7 (.base .int) := by
  have linked := GeneralSourceStateExamples.shadow_cycle_counterexample.1
  have pending : RootPending shadowView loopDemand loopNeeded := by
    apply (pending_graph_iff shadowView loopDemand linked loopNeeded).mpr
    exact ⟨⟨0, by simp [roles, unaryRole]⟩, 0, rfl, rfl, rfl⟩
  refine ⟨linked, GeneralSourceStateExamples.shadow_cycle_counterexample.2.1, pending,
    pending_excludes_rootK2 shadowView loopDemand loopNeeded pending, ?_, rfl⟩
  simp [GeneralSourceBoundary.GraphK2, CommonRoleGraphBisimulation.RegularAt,
    CommonRoleRegularGraph.StructuralCycleAt, Snapshot.graph, Head.node]

/-- A second ordinary model retains an additional visible field. Replacing
the residual by an empty tail would discard this model. -/
abbrev shadowWiderModel : GeneralSourceState.Assignment := fun source =>
  (if source = 0 then Common.record 7 (.base .int) (Common.required 9 (.base .str))
    else .base .int, Common.rowEmpty)

theorem shadow_residual_model :
    GeneralSourceState.Models shadowState shadowWiderModel ∧
      ObservationModels shadowView shadowWiderModel ∧
      (shadowWiderModel 0).1 = Common.record 7 (.base .int) (Common.required 9 (.base .str)) := by
  have models : GeneralSourceState.Models shadowState shadowWiderModel := by
    apply (GeneralSourceState.models_ordinary _ _).mpr
    apply (PresenceNormalForm.all_append _ _ _ _).mpr
    constructor
    · apply (GeneralSourceState.equationAtoms_exact _ _ _).mpr
      exact Common.equivalent_symm (Common.common_shadowed_head_equivalent 7
        (.base .int) (.base .int) (Common.required 9 (.base .str)))
    · apply (GeneralSourceState.equationAtoms_exact _ _ _).mpr
      exact Common.equivalent_refl _
  exact ⟨models, observation_models shadowView shadowWiderModel models, rfl⟩

end Yulang.GeneralSourceK2Examples
