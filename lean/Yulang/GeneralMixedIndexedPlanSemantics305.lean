import Yulang.GeneralMixedIndexedFrame305
import Yulang.GeneralMixedDiagnosticHead304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedPlanSemantics305
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatPlanData (Same head_schema)
open GeneralNominalCenteredHeadMatEffects (Ready bodySchema compileBody)
open GeneralNominalVersionedEffects231 (BodyHolds bodyVariables ClassEffects)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralDeferredLadderTransport302 (capture_eq binder_eq variables_eq)
open GeneralDeferredLadderOperationalView304 (View requests_iff classes_iff)
variable {roles : Roles.RoleDecls} {a b : State roles} {p q : Plan roles}

theorem body_schema_same (same : Same p q) (target : Nat) (body : Body) :
    bodySchema p target body = bodySchema q target body := by
  cases body <;> simp only [bodySchema,compileBody,same.registry,same.interpretation]

theorem body_same (same : Same p q) (target : Nat) (body : Body) (m : Assignment) :
    BodyHolds p target m body ↔ BodyHolds q target m body := by
  unfold BodyHolds
  rw [body_schema_same same]
  cases body
  · simp only [bodyVariables,variables_eq same]
  · simp only [bodyVariables]
    have variables : GeneralNominalCenteredHeadMatEffects.defaultVariables p m =
        GeneralNominalCenteredHeadMatEffects.defaultVariables q m := by
      funext mode index
      unfold GeneralNominalCenteredHeadMatEffects.defaultVariables
      rw [same.input]
    rw [variables]

theorem ready_forward (raw : View a b) (same : Same p q) (ready : Ready a.core root p) :
    Ready b.core root q := by
  intro output listed
  obtain ⟨body,looked,known⟩ := ready output ((requests_iff raw root output).mpr listed)
  exact ⟨body,same.declaration ▸ looked,body_schema_same same output.target body ▸ known⟩

theorem classes_forward (raw : View a b) (same : Same p q) (m : Assignment)
    (valid : ClassEffects a.core root p m) : ClassEffects b.core root q m := by
  have moved := (classes_iff raw p root m).mp valid
  refine ⟨?_,moved.2⟩
  intro output listed body looked
  exact (body_same same output.target body m).mp
    (moved.1 output listed body (same.declaration.symm ▸ looked))

theorem head_same (same : Same p q) (m : Assignment) :
    HeadEquations p m ↔ HeadEquations q m := by
  simp only [HeadEquations,same.input,same.declaration,capture_eq same,binder_eq same,
    head_schema same,GeneralNominalVersionedPlans231.SchemaHolds]

theorem sharing_same (same : Same p q) (m : Assignment) :
    GeneralDictionaryHeadSharing220.Holds p m ↔ GeneralDictionaryHeadSharing220.Holds q m := by
  simp only [GeneralDictionaryHeadSharing220.Holds,GeneralDictionaryHeadSharing220.equations,head_schema same]

end Yulang.GeneralMixedIndexedPlanSemantics305
