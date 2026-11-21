import Yulang.GeneralDeclarativeCompoundProbe325
import Yulang.GeneralDeclarativeModeReads325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundFrame325
open GeneralDeclarativeCompoundDecl325
open GeneralDeclarativeCompoundState325
open GeneralDeclarativeCompoundProbe325
open GeneralDeclarationExamples (itemEquation)
open GeneralDeclarativeExampleSource320 (point leaf)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeFrameReadback325 (Frame Recorded sourceNames)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeClauseOrigins325 (Origin)

abbrev parentBase (_ : Nat) : Capture := point 3
abbrev childBase (_ : Nat) : Capture := childArg
abbrev placement : Placement :=
  ⟨fun _ _ => childArg,fun cl n => if cl.id = clause.id ∧ n = itemEquation.id then 5 else 399⟩

theorem exact_emitted : children impl (sourceNames impl placement parentBase) placement = [call] := rfl

theorem compound_origins : Origin final 8 openChild ∧ Origin final 9 openChild ∧ Origin final 10 openChild := by
  have field : (⟨7,openChild⟩ : Equation) ∈ final.equations := ordinary_old (by simp [ordinaryRows])
  have lo : Alias final 8 7 := .forward (ordinary_old (by simp [ordinaryRows]))
  have mid : Alias final 9 8 := .forward (ordinary_old (by simp [ordinaryRows]))
  have hi : Alias final 10 7 := .forward (ordinary_old (by simp [ordinaryRows]))
  exact ⟨⟨7,lo,field⟩,⟨7,.trans mid lo,field⟩,⟨7,hi,field⟩⟩

theorem root_frame (done : Nat → Prop) : Frame final reg interpret (support2 done) demand impl parentBase placement := by
  refine ⟨.cons ⟨root_bounds,.nominal (j := 0) (upperForms := [.variable 7]) outer_trans (lower_trace done) ?_ ?_⟩ .nil,
    fun _ _ => point_bounds 3,?_⟩
  · exact .row (ordinary_old (show (⟨2,openRoot⟩ : Equation) ∈ ordinaryRows by simp [ordinaryRows]))
  · intro pos there
    cases List.mem_singleton.mp there
    exact .refl _
  · intro demanded was
    cases List.mem_singleton.mp was
    constructor
    · refine ⟨[innerCode],rfl,?_⟩
      intro n pat e found code _
      cases n with
      | zero =>
        have p : inner = pat := Option.some.inj found
        have t : innerCode = e := Option.some.inj code
        cases p
        cases t
        exact compound_origins
      | succ n => simp at found
    · intro entry there
      cases List.mem_singleton.mp there
      exact ⟨.variable 1,rfl,fun notDirect => False.elim (notDirect ⟨1,rfl,List.mem_cons_self⟩)⟩

theorem child_frame (done : Nat → Prop) : Frame final reg interpret (support2 done) call leaf childBase placement := by
  refine ⟨.cons ⟨child_bounds,.actual rfl .capture ?_⟩ .nil,fun _ _ => child_bounds,
    fun _ never => False.elim (List.not_mem_nil never)⟩
  intro o here
  cases List.mem_singleton.mp here
  exact .refl _

theorem root_recorded (done : Nat → Prop) : Recorded final reg interpret (support2 done) demand impl parentBase placement :=
  ⟨root_frame done,[parentRow],rfl,fun _ there => List.mem_append_left _ (List.mem_append_right _ there)⟩

theorem child_recorded (done : Nat → Prop) : Recorded final reg interpret (support2 done) call leaf childBase placement :=
  ⟨child_frame done,[childRow],rfl,fun _ there => List.mem_append_right _ there⟩

end Yulang.GeneralDeclarativeCompoundFrame325
