import Yulang.GeneralNominalRebaseChildProduction241

/-! Backward model extension must preserve existing actual centers. This
module transports their finite labels, not endpoint bounds or whole packets.
It provides no producer of the backward extension premise. -/
namespace Yulang.GeneralNominalRebaseLiveLabels241
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (Algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (CountedMeaning Inputs)
open GeneralNominalPatersonLineage (mass)
open CommonNominalFullCarrier (Equivalent subtype_trans)
variable {roles : Roles.RoleDecls} {semantics : Algebra}
variable {first last : Assignment} {site : Site roles} {labels : List Pattern}

def CentersAgree (sites : List (Site roles)) (first last : Assignment) : Prop :=
 ∀ site ∈ sites, ∀ index, Equivalent (first (site.center index)).1 (last (site.center index)).1

theorem counted (same : Equivalent firstValue lastValue)
 (known : CountedMeaning semantics firstValue pattern) : CountedMeaning semantics lastValue pattern :=
 ⟨known.1,known.2.1,subtype_trans same.2 known.2.2.1,subtype_trans known.2.2.2 same.1⟩

theorem inputs (same : ∀ index, Equivalent (first (site.center index)).1 (last (site.center index)).1)
 (known : Inputs semantics first site labels) : Inputs semantics last site labels := by
 obtain ⟨length,values⟩ := known
 exact ⟨length,fun index => counted (same index) (values index)⟩

theorem live_inputs (same : CentersAgree sites first last) (member : site ∈ sites)
 (known : Inputs semantics first site labels) : Inputs semantics last site labels :=
 inputs (same site member) known

def Bounded (registry : Registry) (seed root budget : Nat) (semantics : Algebra)
 (sites : List (Site roles)) (model : Assignment) : Prop :=
 ∀ site ∈ sites, ∃ depth labels,
 GeneralNominalInvocationAncestry.AtDepth registry seed root depth site.occurrence.identity ∧
 Inputs semantics model site labels ∧ depth + mass labels ≤ budget

theorem bounded (same : CentersAgree sites first last)
 (known : Bounded registry seed root budget semantics sites first) :
 Bounded registry seed root budget semantics sites last := by
 intro site member
 obtain ⟨depth,labels,ancestry,values,limit⟩ := known site member
 exact ⟨depth,labels,ancestry,live_inputs same member values,limit⟩

def BackExtension (sites : List (Site roles)) (oldModels newModels : Assignment → Prop) : Prop :=
 ∀ newModel, newModels newModel → ∃ oldModel, oldModels oldModel ∧ CentersAgree sites oldModel newModel

theorem all_models (extension : BackExtension sites oldModels newModels)
 (known : ∀ oldModel, oldModels oldModel → Bounded registry seed root budget semantics sites oldModel) :
 ∀ newModel, newModels newModel → Bounded registry seed root budget semantics sites newModel := by
 intro newModel valid
 obtain ⟨oldModel,oldValid,same⟩ := extension newModel valid
 exact bounded same (known oldModel oldValid)

theorem back_extension_empty (models : ∀ newModel, newModels newModel → ∃ oldModel, oldModels oldModel) :
 BackExtension ([] : List (Site roles)) oldModels newModels := by
 intro newModel valid
 obtain ⟨oldModel,oldValid⟩ := models newModel valid
 exact ⟨oldModel,oldValid,by intro site member; cases member⟩

theorem back_extension_trans (first : BackExtension sites firstModels middleModels)
 (last : BackExtension sites middleModels lastModels) : BackExtension sites firstModels lastModels := by
 intro model valid
 obtain ⟨middle,middleValid,outer⟩ := last model valid
 obtain ⟨old,oldValid,inner⟩ := first middle middleValid
 refine ⟨old,oldValid,?_⟩
 intro site member index
 have one := inner site member index
 have two := outer site member index
 exact ⟨subtype_trans one.1 two.1,subtype_trans two.2 one.2⟩

end Yulang.GeneralNominalRebaseLiveLabels241
