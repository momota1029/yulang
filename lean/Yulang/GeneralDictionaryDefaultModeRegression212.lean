import Yulang.GeneralDictionaryDefaultSharedTargets212

/-! Closed tests of the I40(B) construction interface, not EvidenceNode
counterexamples. In lower mode a nominal reads actual, not lower. -/
namespace Yulang.GeneralDictionaryDefaultModeRegression212
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultModeSupport212

 def resolve : Mode → Nat → Nat
  | .actual, _ => 0
  | .lower, _ => 1
  | .upper, _ => 2
 def expression : Expr := .nominal 7 [.variable 0]
 def equation : Equation := ⟨1,.lower,expression⟩
 def schema : Schema := ⟨[equation],false⟩

 theorem exact_read : reads resolve .lower expression = [0] := rfl
 theorem targets_unique : (schema.equations.map Equation.target).Nodup := by decide +kernel
 theorem mode_independent : Independent resolve schema.equations := by
  intro e member n used
  cases List.mem_singleton.mp member
  cases List.mem_singleton.mp used
  decide +kernel
 theorem not_all_modes_independent :
     ¬ GeneralNominalCenteredHeadMatExtension.Independent resolve schema.equations := by
  intro allModes
  have bad := allModes equation (List.mem_singleton_self _) .lower 0 (List.mem_singleton_self _)
  exact bad (List.mem_singleton_self _)
 theorem constructed (before : Assignment) :
     schema.Holds (GeneralNominalCenteredHeadMatExtension.sources resolve
       (GeneralNominalCenteredHeadMatExtension.extend resolve before schema.equations))
       (GeneralNominalCenteredHeadMatExtension.extend resolve before schema.equations) :=
  extend_holds targets_unique mode_independent

def duplicateSchema : Schema := ⟨[equation,equation],false⟩

theorem duplicated_targets : ¬ (duplicateSchema.equations.map Equation.target).Nodup := by decide +kernel

theorem duplicate_independent : Independent resolve duplicateSchema.equations := by
 intro e member n used
 have equal : e = equation := by simpa [duplicateSchema] using member
 subst e
 cases List.mem_singleton.mp used
 decide +kernel

theorem duplicate_compatible (before : Assignment) :
    GeneralDictionaryDefaultSharedTargets212.Compatible resolve before duplicateSchema.equations := by
 intro a one b two _
 have first : a = equation := by simpa [duplicateSchema] using one
 have last : b = equation := by simpa [duplicateSchema] using two
 subst a; subst b
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem duplicate_constructed (before : Assignment) :
    duplicateSchema.Holds (GeneralNominalCenteredHeadMatExtension.sources resolve
      (GeneralNominalCenteredHeadMatExtension.extend resolve before duplicateSchema.equations))
      (GeneralNominalCenteredHeadMatExtension.extend resolve before duplicateSchema.equations) :=
 GeneralDictionaryDefaultSharedTargets212.extend_holds duplicate_independent (duplicate_compatible before)

end Yulang.GeneralDictionaryDefaultModeRegression212
