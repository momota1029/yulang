import Yulang.GeneralDeclarativeRepeatGraph327
import Yulang.GeneralDeclarativeProjectedFrame326

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralDeclarativeRepeatFrame327
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeRepeatState327
open GeneralDeclarativeRepeatProbe327
open GeneralDeclarativeRepeatGraph327
open GeneralDeclarativeProjectedFrame326 (Frame)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeClauseOrigins325 (Origin)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeGrowth327 (Extends derives)
open GeneralDeclarativeRepeatedHead327 (original_grows)
open GeneralDeclarativeLowerKnown321 (alias_refl)

theorem repeated_input : (sourceNames impl place base).input 0 = combined := rfl
theorem explicit_output : (sourceNames impl place base).output 1 = 5 := rfl

theorem actual_source : Derives result (.variable 1) mid := by
  apply derives (s := initial) ?_ shared_root
  refine ⟨fun _ no => False.elim (List.not_mem_nil no),fun _ h => ?_,fun _ h => ?_⟩
  · rw [checked_intervals]
    change _ ∈ [(0,1),(1,2)] at h
    rcases List.mem_cons.mp h with rfl|h
    · exact List.mem_cons_self
    cases List.mem_singleton.mp h
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [exact_rows]
    exact List.mem_append_left _ (List.mem_append_left _ h)

theorem original_center_reference : Derives result (.variable 7) (.variable combined.center) := by
  apply Derives.symm
  apply Derives.row
  rw [exact_rows]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem row_member {e : Equation} (found : e ∈ inputRows) : e ∈ result.equations := by
  exact List.mem_append_left _ (List.mem_append_left _ (base_row (List.mem_append_right _ found)))

theorem compound_read : Origin result argC.lower (.nominal 0 [.variable 13]) ∧
    Origin result argC.center (.nominal 0 [.variable 13]) ∧
    Origin result argC.upper (.nominal 0 [.variable 13]) := by
  refine ⟨⟨20,alias_refl _,row_member ?_⟩,⟨21,alias_refl _,row_member ?_⟩,
    ⟨22,alias_refl _,row_member ?_⟩⟩
  · rw [input_exact]; exact List.mem_cons_self
  · rw [input_exact]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [input_exact]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem parent_frame (done : Nat → Prop) :
    Frame result reg interp (supported done) root impl base place := by
  refine ⟨.cons ⟨root_interval,.projected rfl actual_source .capture .capture ?_⟩ .nil,
    fun _ _ => center_of_merge,?_,[rootRow],rfl,?_⟩
  · intro use seen
    change use ∈ [_,_] at seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with rfl|rfl <;> exact original_center_reference
  · intro cl found
    cases List.mem_singleton.mp found
    constructor
    · refine ⟨[compoundCode],rfl,?_⟩
      intro pos p e walked written _
      cases pos with
      | zero =>
        have h : compound = p := Option.some.inj walked
        have k : compoundCode = e := Option.some.inj written
        subst p; subst e
        exact compound_read
      | succ n => simp at walked
    · intro req appears
      cases List.mem_singleton.mp appears
      exact ⟨.variable 1,rfl,fun notDirect => False.elim (notDirect ⟨1,rfl,List.mem_cons_self⟩)⟩
  · intro row h
    exact List.mem_append_left _ (List.mem_append_right _ h)

abbrev childBase (_ : Nat) := argC

theorem child_frame (done : Nat → Prop) :
    Frame result reg interp (supported done) child GeneralDeclarativeExampleSource320.leaf childBase place := by
  refine ⟨.cons ⟨child_interval,.ordinary (.actual rfl .capture ?_)⟩ .nil,
    fun _ _ => child_interval,fun _ empty => False.elim (List.not_mem_nil empty),[childRow],rfl,?_⟩
  · intro use read
    cases List.mem_singleton.mp read
    exact .refl _
  · intro row h
    exact List.mem_append_right _ h

end Yulang.GeneralDeclarativeRepeatFrame327
