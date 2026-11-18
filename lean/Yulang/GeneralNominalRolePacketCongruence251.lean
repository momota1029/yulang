import Yulang.GeneralNominalRolePacket251
namespace Yulang.GeneralNominalRolePacketCongruence251
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRoleEnvironment251
open GeneralNominalCenters (Plan)
open GeneralDeclarations (Clause)
open GeneralNominalAssignmentCongruence238 (subtype_iff)
open CommonNominalFullCarrier

theorem request_related (same : Related first last)
 (catalogue : GeneralDeclarationPatterns.Constructors) (interpretation : GeneralNominalInspection.Interpretation)
 (outputs : List Nat) (assignment : Assignment) (request : GeneralNominalRoleRequests251.Request) :
 GeneralNominalRoleRequests251.Holds catalogue interpretation outputs first assignment request ↔
 GeneralNominalRoleRequests251.Holds catalogue interpretation outputs last assignment request := by
 unfold GeneralNominalRoleRequests251.Holds
 apply forall_congr'; intro expression
 apply forall_congr'; intro _translated
 exact GeneralNominalRawCongruence238.equiv_iff ⟨subtype_refl _,subtype_refl _⟩
   (GeneralDictionaryDefaultExpression209.value_equivalent expression (fun mode name _ => variables_related same outputs mode name))

theorem binder_related (same : Related first last) (name : Nat) :
 GeneralNominalRolePacket251.BinderHolds first name ↔ GeneralNominalRolePacket251.BinderHolds last name :=
 and_congr (subtype_iff (same.lower name) (same.binder name)) (subtype_iff (same.binder name) (same.upper name))

theorem argument_related (same : Related first last) (plan : Plan roles) (clause : Clause)
 (valid : clause.Signature roles) (index : Fin (roles clause.role).arity) :
 GeneralNominalRoleChild251.ArgumentHolds plan first clause valid index ↔
 GeneralNominalRoleChild251.ArgumentHolds plan last clause valid index := by
 unfold GeneralNominalRoleChild251.ArgumentHolds
 cases GeneralDeclarationPatterns.normalize (GeneralNominalRoleChild251.pattern clause valid index)
 case var name => exact binder_related same name
 all_goals
   exact and_congr (subtype_iff (same.target _).1 (same.target _).1)
     (subtype_iff (same.target _).1 (same.target _).1)

theorem child_related (same : Related first last) (plan : Plan roles) (env : Syntax) (assignment : Assignment)
 (clause : Clause) (valid : clause.Signature roles) :
 GeneralNominalRoleChild251.Holds plan env first assignment clause valid ↔
 GeneralNominalRoleChild251.Holds plan env last assignment clause valid := by
 unfold GeneralNominalRoleChild251.Holds
 exact and_congr (forall_congr' fun index => argument_related same plan clause valid index)
   (forall_congr' fun request => forall_congr' fun _ => request_related same _ _ _ assignment request)

theorem packet_related (same : Related first last) (plan : Plan roles) (env : Syntax) (assignment : Assignment) :
 GeneralNominalRolePacket251.Holds plan env first assignment ↔
 GeneralNominalRolePacket251.Holds plan env last assignment := by
 unfold GeneralNominalRolePacket251.Holds
 apply and_congr (by rw [same.old])
 apply and_congr (by rw [same.old])
 apply and_congr (by rw [same.old])
 apply and_congr (by rw [same.old])
 apply and_congr (forall_congr' fun name => forall_congr' fun _ => binder_related same name)
 apply and_congr (GeneralNominalRoleSchema251.holds_related same _ _)
 apply and_congr
 · exact forall_congr' fun clause => forall_congr' fun _ => forall_congr' fun valid => child_related same plan env assignment clause valid
 · exact forall_congr' fun request => forall_congr' fun _ => request_related same _ _ _ assignment request
end Yulang.GeneralNominalRolePacketCongruence251
