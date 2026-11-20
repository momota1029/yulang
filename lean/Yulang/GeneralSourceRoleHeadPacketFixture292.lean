import Yulang.GeneralSourceRoleHeadPacketRun292
import Yulang.GeneralSourceRoleOperationalFixture292

/-! A modeled full head walk and direct declaration feed the unchanged old
Index goal. The CST descriptors here are supplied controls, not Rust output. -/
namespace Yulang.GeneralSourceRoleHeadPacketFixture292
open GeneralSourceRoleHeadPacketRun292 (Source run Origin assoc_exact)
open GeneralSourceRoleResolverFixture292 (localEnv parameterTable role_parameter_used_by_actual_reader)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles
open Roles.Examples (str int)
open Roles.AssocExamples (index omittedImpl omitted_paterson singletonEnv)

def input : Source Unit :=
  ⟨(),⟨.simple "Index",[.binder "'container",.binder "'key"],true⟩,
    [.other,.typeDecl ⟨"value",true,.binder "'key",true⟩]⟩

def view : Unit → Environment := fun _ => localEnv

theorem complete_packet_same_table : run view 2 [input] = some parameterTable := rfl

theorem exact_source_read :
    Origin view [input] 2 0 (some (.var 1)) :=
  (assoc_exact view 2 [input] parameterTable complete_packet_same_table 2 0 _).mp rfl

theorem complete_packet_actual_old_consumer :
    ∀ table : RoleSource, run view 2 [input] = some table →
      assocOf (singletonEnv omittedImpl) (roleTable table) omitted_paterson (index str int) 0 = some int := by
  intro out same
  have e := Option.some.inj (same.symm.trans complete_packet_same_table)
  subst out
  exact role_parameter_used_by_actual_reader

def unsupportedHead : Source Unit :=
  { input with head := ⟨.simple "Index",[.other,.binder "'key"],true⟩ }

theorem malformed_position_cannot_be_silently_shortened : (run view 2 [unsupportedHead]).isNone = true :=
  by decide

#guard (run view 2 [input]).isSome
#guard (run view 2 [unsupportedHead]).isNone

end Yulang.GeneralSourceRoleHeadPacketFixture292
