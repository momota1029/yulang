import Yulang.GeneralNominalVersionedMixedSourceBoundary234
import Yulang.GeneralRebaseDisplayStep276
import Yulang.GeneralNominalExamples

/-! Closed checks diagnosing the next adapter task, not an invariance theorem. -/
namespace Yulang.Cycle276EncodingDiagnostic
open GeneralDeclarations
open GeneralDeclarationExamples (display wrap)
open GeneralNominalExamples (registry intDisplay)
open GeneralNominalCenteredHeadAllocEncoding (declaration)
abbrev compiled := GeneralNominalCenteredHeadAllocEncoding.registry registry

example : declaration display = display := rfl
example : declaration intDisplay = intDisplay := rfl
example : compiled.declarations.filter (fun d => d.role == 0) = [intDisplay,display] := rfl
example : (declaration wrap).outputBinders.map (fun b => b.equation) = [1701] := rfl
example : wrap.outputBinders.map (fun b => b.equation) = [21] := rfl
example : compiled ≠ registry := by
  intro same
  have keys := congrArg (fun r : Registry => r.declarations.flatMap (fun d =>
    d.outputBinders.map (fun b => b.equation))) same
  have bad : (1701 : Nat) = 21 := List.cons.inj keys |>.1
  omega

-- The original source initial predicate is definitionally identical.
example : (GeneralNominalVersionedMixedSourceBoundary234.boundary GeneralDeclarationExamples.roles).Initial
    registry GeneralNominalExamples.displayRoot GeneralRebaseDisplayFrame276.before :=
  GeneralRebaseDisplayStep276.initial_source

-- The consuming relation is literally the mixed Step at the compiled registry.
example (s t : GeneralNominalVersionedJournal232.State GeneralDeclarationExamples.roles) :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary GeneralDeclarationExamples.roles).Step
      registry GeneralNominalExamples.displayRoot s t ↔
    GeneralNominalVersionedMixedKernel234.Step compiled GeneralNominalExamples.displayRoot s t := Iff.rfl

/-- To bridge the encoded adapter, only actual install successors need to be
carried between registries. The other source-kernel constructors coincide. -/
theorem transferStep {a b : Registry} {roles : Roles.RoleDecls}
    {before after : GeneralNominalVersionedJournal232.State roles}
    {root : GeneralSourceDictionaries.Occurrence roles}
    (transfer : ∀ e : GeneralNominalVersionedJournal232.Effect roles,
      GeneralNominalVersionedMixedKernel234.Installable a before e →
      ¬ GeneralNominalVersionedMixedKernel234.Committed before e.plan →
      GeneralNominalVersionedMixedKernel234.At b before e.plan.packet.site.occurrence
        (GeneralNominalVersionedInstall232.install before e)) :
    GeneralNominalVersionedMixedKernel234.Step a root before after →
      GeneralNominalVersionedMixedKernel234.Step b root before after := by
  rintro ⟨focus,generated,action⟩
  refine ⟨focus,generated,?_⟩
  cases action with
  | administrative step => exact .administrative step
  | refresh focus ctx cert src tracked unobserved known =>
    exact .refresh focus ctx cert src tracked unobserved known
  | install effect ready novel => exact transfer effect ready novel
  | merge first last firstPresent lastPresent common novel =>
    exact .merge first last firstPresent lastPresent common novel

/-- The raw journal stores the effect's registry. Kernel results at distinct
registries cannot use identical raw successor states after the same prefix. -/
theorem install_registry_ne {roles : Roles.RoleDecls}
    (before : GeneralNominalVersionedJournal232.State roles)
    (e₁ e₂ : GeneralNominalVersionedJournal232.Effect roles)
    (different : e₁.registry ≠ e₂.registry) :
    GeneralNominalVersionedInstall232.install before e₁ ≠
      GeneralNominalVersionedInstall232.install before e₂ := by
  intro same
  have effects := congrArg GeneralNominalVersionedJournal232.State.effects same
  have first : e₁ = e₂ := (List.cons.inj effects).1
  exact different (congrArg GeneralNominalVersionedJournal232.Effect.registry first)

/-- The installed legacy core only depends on the selected plan. -/
theorem install_core_eq {roles : Roles.RoleDecls}
    (before : GeneralNominalVersionedJournal232.State roles)
    (e₁ e₂ : GeneralNominalVersionedJournal232.Effect roles)
    (same : e₁.plan = e₂.plan) :
    (GeneralNominalVersionedInstall232.install before e₁).core =
      (GeneralNominalVersionedInstall232.install before e₂).core :=
  congrArg (GeneralNominalVersionedInstall232.installCore before.core) same

/-- Same plan and source snapshot give the same model predicate, even when
the registry fields make the stored effects (and raw states) unequal. -/
theorem install_models_equiv {roles : Roles.RoleDecls}
    (before : GeneralNominalVersionedJournal232.State roles)
    (e₁ e₂ : GeneralNominalVersionedJournal232.Effect roles)
    (plan : e₁.plan = e₂.plan) (snapshot : e₁.snapshot = e₂.snapshot)
    (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalVersionedJournal232.Models (GeneralNominalVersionedInstall232.install before e₁) m ↔
    GeneralNominalVersionedJournal232.Models (GeneralNominalVersionedInstall232.install before e₂) m := by
  have core := install_core_eq before e₁ e₂ plan
  have held : e₁.Holds m ↔ e₂.Holds m := by
    unfold GeneralNominalVersionedJournal232.Effect.Holds
    rw [plan,snapshot]
  have live : ∀ c, e₁.Live c m ↔ e₂.Live c m := by
    intro c
    unfold GeneralNominalVersionedJournal232.Effect.Live
    rw [plan]
  simp only [GeneralNominalVersionedJournal232.Models,GeneralNominalVersionedInstall232.install,
    List.forall_mem_cons]
  change (_ ∧ (_ ∧ _) ∧ ((_ ∧ _) ∧ _)) ↔ (_ ∧ (_ ∧ _) ∧ ((_ ∧ _) ∧ _))
  rw [plan,held,live]

end Yulang.Cycle276EncodingDiagnostic
