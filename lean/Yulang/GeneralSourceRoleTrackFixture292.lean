import Yulang.GeneralSourceRoleTrack292
import Yulang.GeneralSourceRoleHeadPacketFixture292

/-! Occurrence labels in a synthetic input are preserved but do not affect
the real association reader's numeric values or identify Rust source nodes. -/
namespace Yulang.GeneralSourceRoleTrackFixture292
open GeneralSourceRoleTrack292
open GeneralSourceRoleHeadPacketFixture292 (input view)
open GeneralSourceRoleResolverFixture292 (parameterTable role_parameter_used_by_actual_reader)
open GeneralSourceRoleExport292 (Aligned)
open GeneralSourceRoleSpelling292 (Body ResolvedBody Position)
open GeneralSourceMetadataRoles291 (RoleSource roleTable)
open Roles
open Roles.Examples (str int)
open Roles.AssocExamples (index omittedImpl omitted_paterson singletonEnv)

def marked : Tracked Unit Nat :=
  ⟨(),input.head,100,[(101,.other),(102,.typeDecl ⟨"value",true,.binder "'key",true⟩)]⟩

def moved : Tracked Unit Nat := { marked with
  atRole := 200, body := marked.body.map (fun c => (c.1 + 100,c.2)) }

theorem handle_moves_leave_table :
    runTracked view 2 [marked] = some parameterTable ∧
    runTracked view 2 [moved] = some parameterTable := ⟨rfl,rfl⟩

theorem carrying_positions : OriginAt view [marked] 2 0 (some (.var 1)) 100 102 := by
  refine ⟨marked,List.mem_singleton_self _,rfl,"Index",["'container","'key"],?_,rfl,
    ⟨"value",true,.binder "'key",true⟩,?_,⟨"value",.binder "'key"⟩,.binder _ _,rfl,?_⟩
  · exact ⟨rfl,rfl,.cons rfl (.cons rfl .nil)⟩
  · decide
  · exact .binder (.rest (by decide) .first)

theorem non_type_handle_not_origin : ¬ OriginAt view [marked] 2 0 (some (.var 1)) 100 101 := by
  rintro ⟨candidate,onList,_,_,_,_,_,child,bodyHit,_,_,_,_⟩
  have same := List.mem_singleton.mp onList
  subst candidate
  change (101, GeneralSourceRoleChildCoverage292.Child.typeDecl child) ∈
    [(101,.other),(102,.typeDecl ⟨"value",true,.binder "'key",true⟩)] at bodyHit
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at bodyHit
  rcases bodyHit with ⟨_,impossible⟩ | ⟨impossible,_⟩ <;> cases impossible

theorem readback_preserved_after_handle_move :
    ∀ table : RoleSource, runTracked view 2 [moved] = some table →
      assocOf (singletonEnv omittedImpl) (roleTable table) omitted_paterson (index str int) 0 = some int := by
  intro table exactTable
  have eq := Option.some.inj (exactTable.symm.trans handle_moves_leave_table.2)
  subst table
  exact role_parameter_used_by_actual_reader

end Yulang.GeneralSourceRoleTrackFixture292
