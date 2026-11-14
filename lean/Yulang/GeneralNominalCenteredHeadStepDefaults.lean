import Yulang.GeneralNominalCenteredHeadStepBoundary
import Yulang.GeneralDictionaryAssociatedProvenance
import Yulang.GeneralDictionarySupportRecursiveExample

set_option backward.isDefEq.respectTransparency false

/-! The explicit-schema readiness predicate excludes a legal positional
default. The example is an inhabited, source-formed ground initial state.
It does not refute an implication that assumes the old positive baseline. -/
namespace Yulang.GeneralNominalCenteredHeadStepDefaults
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepEffects (State Models initial)
open GeneralNominalExamples (context state interpretation model state_models)
open GeneralDeclarationExamples (constructors)

def roles : Roles.RoleDecls := fun _ =>
  { arity := 1
    assoc := fun name => if name = 0 then some (some (.var 0)) else none
    defaultsScoped := by
      intro name rhs found
      split at found
      · cases found; simp [Roles.Term.bound]
      · cases found }

abbrev declaration : Declaration := ⟨27,0,[.app 2 []],[],[],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
def root : Occurrence roles := ⟨100,⟨0,fun _ => (1,1),[⟨0,1⟩],by
  intro output member
  cases List.mem_singleton.mp member
  exact ⟨some (.var 0),rfl⟩⟩⟩
abbrev start := initial (context true) root

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,by simp,?_,by simp⟩
    intro name body found
    change (if name = 0 then some (some (Roles.Term.var 0)) else none) = some body at found
    split at found
    · cases found; exact Or.inr rfl
    · cases found
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · simp
  · simp
  · simp
  · simp

theorem checked : Checked registry :=
  ⟨by simp,by intro d member; cases List.mem_singleton.mp member; exact declaration_checked⟩

theorem source : GeneralNominalSourceFormation.InitialSource registry (context true) root where
  roles_agree := rfl
  metadata := GeneralDictionarySupportRecursiveExample.initial_source.metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ,root]
    · intro output member
      cases List.mem_singleton.mp member
      simp [GeneralNominalState.sources,List.ofFn_succ]
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := GeneralDictionarySupportRecursiveExample.initial_source.below_seed
  unallocated := rfl

theorem inhabited : Models start model := by
  apply (GeneralNominalCenteredHeadStepEffects.initial_models).mpr
  apply (GeneralNominalCenteredSteps.point_initial_models _ _ (fun _ => rfl) _).mpr
  exact state_models true

theorem ground : GeneralNominalGroundAccessibility.GroundRoots (context true) root [.app 2 []] := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bounded := index.isLt; change index.val < 1 at bounded; omega
  let term : GeneralNominalOriginTerms.Expr Nat := .node (.scalar .int) Fin.elim0
  refine ⟨term,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · simp [normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation,
        GeneralNominalCompoundReadback.quote,term]
    · simp [term,GeneralNominalOriginTerms.Expr.leaves,List.ofFn_zero,
        GeneralNominalOriginTerms.arity]
    · exact ⟨trivial,fun index => Fin.elim0 index⟩
  · intro assignment valid
    exact valid.1.2.1 (1 : Fin 2) (.base .int) rfl

theorem initial_source : (GeneralNominalCenteredHeadStepBoundary.boundary roles).Initial registry root start :=
  ⟨context true,[.app 2 []],source,(fun _ => rfl),ground,rfl⟩

theorem reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadStepBoundary.boundary roles) registry root start :=
  ⟨start,initial_source,.refl⟩

theorem fallback : GeneralDictionaryAssociatedProvenance.lookup roles declaration 0 =
    some (.default 0 0 (.var 0)) := rfl

theorem retained : (⟨0,1⟩ : GeneralSourceState.Output) ∈ requests start.core root :=
  request_retained (GeneralNominalDemandMerging.pointSite root) (List.mem_singleton_self _) (.refl _)
    (List.mem_singleton_self _)

theorem no_ready (plan : Plan roles) (visible : plan.packet.declaration ∈ registry.declarations) :
    ¬ EffectsReady start.core root plan := by
  intro ready
  obtain ⟨equation,member,_⟩ := ready.1 _ retained
  have same : plan.packet.declaration = declaration := List.mem_singleton.mp visible
  rw [same] at member
  cases member

theorem no_chosen_head (key model) : ¬ ChosenHead registry start.core root key model := by
  rintro ⟨_,plan,frame,ready,_⟩
  exact no_ready plan frame.visible ready

theorem no_positive_baseline (key) :
    ¬ ∃ model, Models start model ∧ ChosenHead registry start.core root key model := by
  rintro ⟨model,_,chosen⟩
  exact no_chosen_head key model chosen

theorem no_output_conflict (key) :
    ¬ GeneralNominalCenteredHeadStepBoundary.OutputConflict registry start root key :=
  fun conflict => no_positive_baseline key conflict.1

theorem no_install (plan : Plan roles) (focus : plan.packet.site.occurrence = root) (support) :
    ¬ GeneralNominalCenteredHeadStepKernel.Installable registry start plan support := by
  intro enabled
  exact no_ready plan enabled.frame.visible (focus ▸ enabled.ready)

/-- A retained request without an explicit body blocks the frozen readiness
predicate even when the associated-provenance lookup supplies a default. -/
theorem missing_explicit_blocks {ρ : Roles.RoleDecls} {current : GeneralNominalCenteredSteps.State ρ}
    {focus : Occurrence ρ} {plan : Plan ρ}
    (member : output ∈ requests current focus)
    (missing : ∀ equation ∈ plan.packet.declaration.associated, equation.name ≠ output.name) :
    ¬ EffectsReady current focus plan := by
  rintro ⟨coverage,_⟩
  obtain ⟨equation,present,same⟩ := coverage output member
  exact missing equation present same

theorem recorded_default_blocks_live_ready {ρ : Roles.RoleDecls} {current : State ρ}
    {effect : GeneralNominalCenteredHeadStepEffects.Effect ρ}
    (recorded : effect ∈ current.effects)
    (member : output ∈ requests current.core effect.plan.packet.site.occurrence)
    (missing : ∀ equation ∈ effect.plan.packet.declaration.associated, equation.name ≠ output.name) :
    ¬ GeneralNominalCenteredHeadStepEffects.LiveEffectsReady current :=
  fun ready => missing_explicit_blocks member missing (ready effect recorded)

end Yulang.GeneralNominalCenteredHeadStepDefaults
