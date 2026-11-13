import Yulang.GeneralNominalSharedBudget
import Yulang.GeneralNominalSharedEnumeration

/-! Composition of observational readbacks over a fixed leaf basis. Source
cycles may remain opaque leaves; observation updates do not consume holes. -/
namespace Yulang.GeneralNominalHoleReadback
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSupport GeneralNominalSaturationState

def Over (models : Assignment → Prop) (basis : List Origin) (root : Origin) (term : Expr Origin) : Prop :=
  (∀ model, models model → Holds model term root) ∧ ∀ origin ∈ term.leaves, origin ∈ basis

theorem holds_bind {model : Assignment} (valid : Holds model term root)
    (substitution : Origin → Expr Origin)
    (leaves : ∀ origin ∈ term.leaves, Holds model (substitution origin) origin) :
    Holds model (term.bind substitution) root := by
  induction term generalizing root with
  | leaf origin => exact holds_transport (same_symm valid) (leaves origin (by simp [Expr.leaves]))
  | node test children ih =>
      refine ⟨valid.1,fun index => ih index (valid.2 index) ?_⟩
      intro origin member
      exact leaves origin (by
        simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
        exact ⟨_,⟨index,rfl⟩,member⟩)

theorem compose (readback : Over models middle root term) (substitution : Origin → Expr Origin)
    (represented : ∀ origin ∈ middle, Over models basis origin (substitution origin)) :
    Over models basis root (term.bind substitution) := by
  constructor
  · intro model valid
    exact holds_bind (readback.1 model valid) substitution
      (fun origin member => (represented origin (readback.2 origin member)).1 model valid)
  · intro origin member
    obtain ⟨name,used,member⟩ := (leaves_bind term substitution origin).mp member
    exact (represented name (readback.2 name used)).2 origin member

theorem identity_leaf (member : Origin.source identity ∈ basis) :
    Over models basis (.source identity) (.leaf (.source identity)) :=
  ⟨fun model _ => source_self model identity,by simpa [Expr.leaves]⟩

theorem alias (readback : Over models basis first term)
    (same : ∀ model, models model → Same model first last) : Over models basis last term :=
  ⟨fun model valid => holds_transport (same model valid) (readback.1 model valid),readback.2⟩

theorem project_readback (readback : Over models basis root (.node test children))
    (index : Fin (arity test)) : Over models basis (project root test index) (children index) := by
  refine ⟨fun model valid => (readback.1 model valid).2 index,?_⟩
  intro origin member
  apply readback.2 origin
  simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
  exact ⟨_,⟨index,rfl⟩,member⟩

theorem restrict (readback : Over before basis root term)
    (restriction : ∀ model, after model → before model) : Over after basis root term :=
  ⟨fun model valid => readback.1 model (restriction model valid),readback.2⟩

theorem step_preserves (step : GeneralNominalSharedSteps.Step registry focus before after)
    (readback : Over (Models before.current) basis root term) :
    Over (Models after.current) basis root term :=
  restrict readback (GeneralNominalSharedSteps.step_models step)

theorem trace_preserves (steps : B4Target.Steps (GeneralNominalSharedSteps.Step registry focus) before after)
    (readback : Over (Models before.current) basis root term) :
    Over (Models after.current) basis root term := by
  induction steps with
  | refl => exact readback
  | tail path step ih => exact step_preserves step ih

/-- Refresh and descriptor replacement preserve the same term and leaf list.
Their progress is an observation fact, not necessarily a substitution. -/
theorem refresh_exact (certificate : GeneralNominalFeedbackSteps.Refresh state context) :
    Over (Models (regenerate state context)) basis root term ↔ Over (Models state) basis root term := by
  constructor
  · intro readback
    exact restrict readback (fun model valid => (GeneralNominalCycleSteps.refresh_models certificate model).mpr valid)
  · intro readback
    exact restrict readback (fun model valid => (GeneralNominalCycleSteps.refresh_models certificate model).mp valid)

theorem reobservation_exact (revision : GeneralNominalReobservationSteps.Revision state)
    (certificate : GeneralNominalReobservationSteps.Certified revision) :
    Over (Models revision.result) basis root term ↔ Over (Models state) basis root term :=
  ⟨fun readback => restrict readback (fun model valid => (certificate.exact model).mpr valid),
    fun readback => restrict readback (fun model valid => (certificate.exact model).mp valid)⟩

theorem promoted_over_basis (trusted : GeneralNominalSharedSupport.Trusted state facts readbacks)
    (present : Fact.outputs packet support ∈ facts)
    (output : GeneralSourceState.Output) (member : output ∈ packet.site.occurrence.demand.outputs)
    (substitution : Origin → Expr Origin)
    (represented : ∀ origin ∈ GeneralNominalSharedSupport.inputOrigins facts,
      Over (GeneralNominalSharedSupport.Models state facts) basis origin (substitution origin)) :
    ∃ term, Over (GeneralNominalSharedSupport.Models state facts) basis (.source output.target) term := by
  obtain ⟨term,valid,leaves⟩ := GeneralNominalSharedSupport.promoted_output_readback trusted present output member
  exact ⟨term.bind substitution,compose ⟨valid,leaves⟩ substitution represented⟩

end Yulang.GeneralNominalHoleReadback
