import Yulang.GeneralObservedMetadataExpressions290

/-! Replay the real centered explicit bodies and positional defaults under
certified metadata, leaving the chosen plan and its variables unchanged. -/
namespace Yulang.GeneralObservedMetadataBodies290
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenters (Plan)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateDefault)
open GeneralNominalCenteredHeadMatSchemas (Schema)
open GeneralNominalCenteredHeadMatEffects (compileBody bodySchema BodyHolds bodyVariables)
open GeneralNominalCommonBridge (Assignment)
open GeneralObservedMetadataKeys290 (keys)
open GeneralObservedMetadataExpressions290 (explicit_eq default_eq termKeys)
open GeneralObservedMetadataEntry290 (LocalEqual)

def bodyKeys : Body → List Nat
  | .explicit equation => keys equation.rhs
  | .default _ _ t => termKeys t

def compileFrom (c : Constructors) (i : Interpretation) : Body → Option Expr
  | .explicit equation => translate c i equation.rhs
  | .default _ _ t => translateDefault c i t

theorem compile_current (plan : Plan roles) (body : Body) :
    compileFrom plan.packet.registry.constructors plan.packet.context.interpretation body =
      compileBody plan body := by cases body <;> rfl

theorem compile_eq {c d : Constructors} {i j : Interpretation}
    (b : Body) (h : LocalEqual (bodyKeys b) c i d j) :
    compileFrom c i b = compileFrom d j b := by
  cases b with
  | explicit eq => exact explicit_eq _ _ _ _ eq.rhs h
  | default _ _ t => exact default_eq _ _ _ _ t h

def bodySchemaFrom (c : Constructors) (i : Interpretation) (target : Nat) (body : Body) : Schema :=
  match compileFrom c i body with
  | some expression => ⟨[⟨target,.actual,expression⟩],false⟩
  | none => ⟨[],true⟩

theorem bodySchema_current (plan : Plan roles) (target : Nat) (b : Body) :
    bodySchemaFrom plan.packet.registry.constructors plan.packet.context.interpretation target b =
      bodySchema plan target b := by
  rw [bodySchemaFrom,compile_current,bodySchema]
  rfl

theorem bodySchema_eq (plan : Plan roles) (c : Constructors) (i : Interpretation) (target : Nat) (b : Body)
    (h : LocalEqual (bodyKeys b) plan.packet.registry.constructors plan.packet.context.interpretation c i) :
    bodySchemaFrom c i target b = bodySchema plan target b := by
  rw [← bodySchema_current]
  unfold bodySchemaFrom
  rw [compile_eq b h]

theorem bodyHolds_iff (plan : Plan roles) (c : Constructors) (i : Interpretation) (target : Nat)
    (b : Body) (m : Assignment)
    (h : LocalEqual (bodyKeys b) plan.packet.registry.constructors plan.packet.context.interpretation c i) :
    (bodySchemaFrom c i target b).Holds (bodyVariables plan m b) m ↔ BodyHolds plan target m b := by
  rw [bodySchema_eq plan c i target b h]
  rfl

end Yulang.GeneralObservedMetadataBodies290
