import Yulang.GeneralSourceRoleCstConsumer293
import Yulang.GeneralSourceRoleResolverFixture292

/-! Cross the boundary only with a separate explicit name map. The parser
mirror producer never sees that map or the kernel's numeric role table. -/
namespace Yulang.GeneralSourceRoleCstConsumerFixture293
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstFixture293 (whole required namedBody sigil result)
open GeneralSourceRoleCstSnapshot293
open GeneralSourceRoleTrack292 (runTracked)
open GeneralSourceRoleResolverFixture292
  (localEnv parameterTable role_parameter_used_by_actual_reader)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles
open Roles.AssocExamples (index singletonEnv omittedImpl omitted_paterson)
open Roles.Examples (int str)

def stored : Snapshot Nat := ⟨10,whole (namedBody (sigil "'key"))⟩
def requested : Address Nat := ⟨10,[2]⟩

theorem own_export :
    exportAt () stored requested = some (mark 10 (result (.binder "'key") true)) := rfl

theorem foreign_same_path :
    exportAt () stored (⟨11,[2]⟩ : Address Nat) = none := rfl

theorem unresolved_then_attached :
    ((exportAt () stored requested).bind fun src => runTracked (fun _ => localEnv) 2 [src]) =
      some parameterTable := rfl

theorem existing_index_reads_second_argument :
    ∀ table : RoleSource,
      ((exportAt () stored requested).bind fun src => runTracked (fun _ => localEnv) 2 [src]) =
        some table →
      assocOf (singletonEnv omittedImpl) (roleTable table) omitted_paterson (index str int) 0 =
        some int := by
  intro table compiled
  have exactTable := Option.some.inj (compiled.symm.trans unresolved_then_attached)
  subst table
  exact role_parameter_used_by_actual_reader

#guard (exportAt () stored requested).isSome
#guard (exportAt () stored (⟨11,[2]⟩ : Address Nat)).isNone

end Yulang.GeneralSourceRoleCstConsumerFixture293
