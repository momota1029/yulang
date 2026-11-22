import Yulang.GeneralDeclarativeEndpointResidual336
import Yulang.GeneralDeclarativeWitnessCutDecl334
import Yulang.GeneralDeclarativeRecordSplit330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointCase336
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Bounds HeadMeaning)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessCutDecl334 (arg pat)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordSplit330 (interval hidden no_literal lo hi)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record mask Ty Equivalent exactEmpty)
open PresenceNormalForm (all_nil)

abbrev endCode : Expr := .primitive .exactEmpty []
abbrev loFields : List (Nat × Expr) := [(7,.variable 3)]
abbrev hiFields : List (Nat × Expr) := [(7,.variable 4)]
abbrev rowLo : Equation := ⟨0,.record 7 (.variable 3) endCode⟩
abbrev rowHi : Equation := ⟨2,.record 7 (.variable 4) endCode⟩
abbrev before : State := ⟨⟨[],[(0,1),(1,2)]⟩,[rowLo,rowHi]⟩
def support : Supported before (fun _ => False) :=
  ⟨fun e o => e ∈ before.equations ∧ o = .source,And.left⟩
theorem low : rowLo ∈ (restriction support).equations :=
  from_source support ⟨List.mem_cons_self,rfl⟩
theorem high : rowHi ∈ (restriction support).equations :=
  from_source support ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩

theorem actual_read : Read support arg [7] loFields hiFields loFields hiFields endCode endCode :=
  ⟨⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
   by decide,.inline (alias_refl _) .exactEnd low,.inline (alias_refl _) .exactEnd high,rfl,rfl⟩

theorem center_not_listed : ∀ row ∈ before.equations, row.left ≠ arg.center := by
  intro row seen
  change row ∈ [rowLo,rowHi] at seen
  rcases List.mem_cons.mp seen with rfl|h
  · decide
  · cases List.mem_singleton.mp h
    decide

def model : Assignment := fun n =>
  (if n = 0 then lo 7 else if n = 1 then hidden 7 else if n = 2 then hi 7 else if n = 3 then .bottom else .top,Common.rowEmpty)

theorem model_ok : Models before model := by
  refine ⟨⟨all_nil _ _,?_⟩,?_⟩
  · intro e h
    change e ∈ [(0,1),(1,2)] at h
    rcases List.mem_cons.mp h with rfl|other
    · exact (interval 7).1
    · cases List.mem_singleton.mp other
      exact (interval 7).2
  · intro e h
    change e ∈ [rowLo,rowHi] at h
    rcases List.mem_cons.mp h with rfl|other
    · exact eqv_refl _
    · cases List.mem_singleton.mp other
      exact eqv_refl _

/-- This is an actual approved endpoint read at a fixed normalized
record-binder shape, not just a carrier-level sandwich. The former
literal head evidence is false for this state in a concrete model,
however the future implementation represents the chosen bounds. -/
theorem old_head_impossible (capture : Nat → Capture) :
    ¬ HeadMeaning constructors interpretation capture model arg pat := by
  intro special
  apply no_literal 7 (model (capture 0).center).1 (model (capture 1).center).1
  exact special.1

theorem both (m) (someModel : Models before m) :
    (∃ payload, GeneralDeclarativeRecordChannel330.project 7 false [] (m 1).1 = some payload ∧
      GeneralDeclarativeWhere319.InInterval (m 3).1 (m 4).1 payload) ∧
    GeneralDeclarativeWhere319.InInterval (mask [7] exactEmpty) (mask [7] exactEmpty)
      (mask [7] (m 1).1) := by
  exact ⟨GeneralDeclarativeEndpointRecord336.field_interval actual_read List.mem_cons_self
    List.mem_cons_self m someModel,GeneralDeclarativeEndpointResidual336.exact_residuals actual_read m someModel⟩

end Yulang.GeneralDeclarativeEndpointCase336
