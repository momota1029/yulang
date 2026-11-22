import Yulang.GeneralStoppedInstallHistory335
import Yulang.GeneralStoppedProjectedTrace335
import Yulang.GeneralDeclarativeSubstitution320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedOutput339
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Output)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenteredHeadMatEffects (compileBody bodySchema Ready BodyHolds)
open GeneralNominalVersionedEffects231 (body_holds_iff)
open GeneralNominalCenters (Plan)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralDeclarativeEntailment320 (Holds appendFacts model_append)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralStoppedInstallHistory335 (InstalledBetween saved_projection)
open GeneralStoppedProjectedTrace335 (normalized)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open B4Target (Steps)

def captureFor (plan : Plan roles) : Body → Nat → Capture
  | .explicit _ => fun name => point (plan.binder name)
  | .default .. => fun index => point ((List.ofFn plan.input.center)[index]?.getD 0)

def ordinary (plan : Plan roles) (output : Output) (body : Body) : Option Equation :=
  (compileBody plan body).map fun rhs => ⟨output.target,logical (captureFor plan body) .actual rhs⟩

theorem names_actual (plan : Plan roles) (m : Assignment) (body : Body) (n : Nat) :
    variables (captureFor plan body) m .actual n =
    GeneralNominalCenteredHeadMatEffects.bodyVariables plan m body .actual n := by
  cases body with
  | explicit eq =>
    simp only [captureFor,GeneralNominalCenteredHeadMatEffects.bodyVariables,
      GeneralNominalCenteredHeadMatEffects.variables]
    split <;> rfl
  | default => rfl

/-- The exact compiled fixed output uses the same actual names as the
live versioned body. Defaults use the actual input center table;
explicit outputs use the actual binder table, not a bound endpoint. -/
theorem ordinary_holds {plan : Plan roles} {output : Output} {body : Body}
    (computed : ordinary plan output body = some row) (fitted : BodyHolds plan output.target m body) :
    Holds m row := by
  unfold ordinary at computed
  obtain ⟨expression,compiled,rfl⟩ := Option.map_eq_some_iff.mp computed
  unfold BodyHolds bodySchema at fitted
  rw [compiled] at fitted
  have semantic := fitted _ List.mem_cons_self
  change Equivalent (m output.target).1
    (value (GeneralNominalCenteredHeadMatEffects.bodyVariables plan m body) .actual expression) at semantic
  change Equivalent (m output.target).1
    (value (environment m) .actual (logical (captureFor plan body) .actual expression))
  rw [logical_value]
  rw [GeneralNominalVersionedEffects231.actual_value
    (variables (captureFor plan body) m) (GeneralNominalCenteredHeadMatEffects.bodyVariables plan m body)
    (names_actual plan m body) expression]
  exact semantic

theorem fixed_target {plan : Plan roles} {output : Output} {body : Body}
    (computed : ordinary plan output body = some row) : row.left = output.target := by
  unfold ordinary at computed
  obtain ⟨_,_,rfl⟩ := Option.map_eq_some_iff.mp computed
  rfl

structure Receipt {roles : Roles.RoleDecls} (final : State roles) (effect : Effect roles)
    (output : Output) (row : Equation) : Prop where
  requested : output ∈ requests final.core effect.plan.packet.site.occurrence
  authored : ∃ body, lookup roles effect.plan.packet.declaration output.name = some body ∧
    ordinary effect.plan output body = some row

theorem row_present {final : State roles} {effect : Effect roles}
    (retained : effect ∈ final.effects) (found : Receipt final effect output row)
    (fit : Models final m) : Holds m row ∧ row.left = output.target := by
  obtain ⟨body,selected,compiled⟩ := found.authored
  have current := (GeneralNominalVersionedJournal232.effect_models fit retained).2
  have exact := (body_holds_iff effect.plan output.target m body).mp (current.1 output found.requested body selected)
  exact ⟨ordinary_holds compiled exact,fixed_target compiled⟩

theorem ready_rhs {s : State roles} {effect : Effect roles}
    (known : Ready s.core effect.plan.packet.site.occurrence effect.plan)
    (requested : output ∈ requests s.core effect.plan.packet.site.occurrence) :
    ∃ row, Receipt s effect output row := by
  obtain ⟨body,got,recognized⟩ := known output requested
  cases h : compileBody effect.plan body with
  | none => simp [bodySchema,h] at recognized
  | some rhs => exact ⟨⟨output.target,logical (captureFor effect.plan body) .actual rhs⟩,requested,body,got,by simp [ordinary,h]⟩

/-- A current compiled row preserves its genuine versioned install
origin and literal target through an actual raw path. The old ordinary
projection may be enriched by these exact known rows, without
claiming either complete coverage or converse journal model recovery. -/
theorem append_current {registry : Registry} {root : Occurrence roles}
    {start final : State roles} (path : Steps (Step registry root) start final)
    (empty : start.effects = []) (lowered : normalized final = some ordinaryState)
    (recognized : ∀ row ∈ added, ∃ effect ∈ final.effects, ∃ output, Receipt final effect output row)
    (m : Assignment) (fit : Models final m) :
    GeneralDeclarativeHead320.Models (appendFacts ordinaryState added) m ∧
    ∀ row ∈ added, ∃ effect ∈ final.effects, ∃ output,
      InstalledBetween registry root start final effect ∧ Receipt final effect output row ∧
      row.left = output.target := by
  have current := (GeneralStoppedLower335.exact_models _ m lowered).mpr fit.1.1
  refine ⟨(model_append m).mpr ⟨current,?_⟩,?_⟩
  · intro row there
    obtain ⟨effect,present,_,recorded⟩ := recognized row there
    exact (row_present present recorded fit).1
  · intro row there
    obtain ⟨effect,present,output,recorded⟩ := recognized row there
    obtain ⟨origin,_,_⟩ := saved_projection path empty present fit
    exact ⟨effect,present,output,origin,recorded,(row_present present recorded fit).2⟩

end Yulang.GeneralDeclarativeStoppedOutput339
