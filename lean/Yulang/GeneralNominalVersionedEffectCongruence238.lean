import Yulang.GeneralNominalVersionedPacketCongruence238
import Yulang.GeneralNominalVersionedJournal232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedEffectCongruence238
open GeneralNominalAssignmentCongruence238 (Same)
open GeneralNominalRawCongruence238 (equiv_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalVersionedEffects231
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem body_variables (same : Same first last) (plan : Plan roles)
 (body : GeneralDictionaryAssociatedProvenance.Body) (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
 Equivalent (bodyVariables plan first body mode name) (bodyVariables plan last body mode name) := by
 cases body with
 | explicit => exact GeneralNominalSchemaCongruence238.variables same plan mode name
 | default => exact (same _).1

theorem body_iff (same : Same first last) (plan : Plan roles) (target : Nat)
 (body : GeneralDictionaryAssociatedProvenance.Body) :
 BodyHolds plan target first body ↔ BodyHolds plan target last body :=
 GeneralNominalSchemaCongruence238.total_schema_iff same _ _ (body_variables same plan body) _

theorem class_iff (same : Same first last) (state : GeneralNominalCenteredSteps.State roles)
 (root : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) :
 ClassEffects state root plan first ↔ ClassEffects state root plan last := by
 apply and_congr
 · apply forall_congr'; intro output
   apply forall_congr'; intro member
   apply forall_congr'; intro body
   apply forall_congr'; intro found
   exact body_iff same plan output.target body
 · apply forall_congr'; intro a
   apply forall_congr'; intro one
   apply forall_congr'; intro b
   apply forall_congr'; intro two
   apply forall_congr'; intro named
   exact equiv_iff (same _).1 (same _).1

theorem effect_iff (same : Same first last) (state : State roles) (effect : Effect roles) :
 (effect.Holds first ∧ effect.Live state.core first) ↔ (effect.Holds last ∧ effect.Live state.core last) :=
 and_congr
   (and_congr (GeneralNominalProjectionCongruence238.head_models_iff same _)
     (class_iff same _ _ _)) (class_iff same _ _ _)
end Yulang.GeneralNominalVersionedEffectCongruence238
