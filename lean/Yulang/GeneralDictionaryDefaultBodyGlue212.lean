import Yulang.GeneralDictionaryDefaultAvailability208
import Yulang.GeneralDictionaryDefaultTotalFrame212

/-! Ready explicit/default bodies make same-name output equality a consequence
of their body equations. No arbitrary output values are identified. -/
namespace Yulang.GeneralDictionaryDefaultBodyGlue212
open GeneralNominalCenters GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalCenteredHeadMatExpressions
open GeneralDictionaryAssociatedProvenance
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {plan : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem compiled (complete : (bodySchema plan target body).unknown = false) :
     ∃ expression, compileBody plan body = some expression := by
  cases found : compileBody plan body with
  | none => simp [bodySchema,found] at complete
  | some expression => exact ⟨expression,rfl⟩

 theorem same_body (complete : (bodySchema plan first body).unknown = false)
     (one : BodyHolds plan first model body) (two : BodyHolds plan last model body) :
     Equivalent (model first).1 (model last).1 := by
  obtain ⟨expression,found⟩ := compiled complete
  have a := (body_equation found).mp one
  have b := (body_equation found).mp two
  exact ⟨subtype_trans a.1 b.2,subtype_trans b.1 a.2⟩

 theorem equal_outputs
     (ready : Ready state focus plan)
     (bodies : ∀ output ∈ requests state focus, ∀ body,
       lookup roles plan.packet.declaration output.name = some body → BodyHolds plan output.target model body) :
     EqualOutputs state focus model := by
  intro first one last two named
  obtain ⟨body,found,complete⟩ := ready first one
  exact same_body complete (bodies first one body found)
    (bodies last two body (named ▸ found))

 theorem class_iff_bodies (ready : Ready state focus plan) :
     ClassEffects state focus plan model ↔
     ∀ output ∈ requests state focus, ∀ body,
       lookup roles plan.packet.declaration output.name = some body → BodyHolds plan output.target model body :=
  ⟨And.left,fun bodies => ⟨bodies,equal_outputs ready bodies⟩⟩

/-- For an actual selected effect, the snapshot class equality conjunct is
therefore derived from all explicit/default body equations. -/
 theorem effect_iff_bodies (effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles) :
     effect.Holds model ↔ GeneralNominalCenteredHeadOutputs.HeadEquations effect.plan model ∧
       ∀ output ∈ requests effect.snapshot effect.plan.packet.site.occurrence, ∀ body,
         lookup roles effect.plan.packet.declaration output.name = some body →
           BodyHolds effect.plan output.target model body :=
  and_congr Iff.rfl (class_iff_bodies effect.ready)

end Yulang.GeneralDictionaryDefaultBodyGlue212
