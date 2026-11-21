import Yulang.GeneralDeclarativeCurrentProbe330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentResult330
open GeneralDeclarativeRepeatDecl327 (reg impl root checked)
open GeneralDeclarativeArityFixture330 hiding final returnRow root_range_now child_range
open GeneralDeclarativeCurrentProbe330
open GeneralDeclarativeCurrentReceipt330 (Rule Receipt dictionary complete relays_models)
open GeneralDeclarativeArityResult330 (root_only child_only dict declared)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Models)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev oldFinal := GeneralDeclarativeArityFixture330.final
abbrev oldReturn := GeneralDeclarativeArityFixture330.returnRow
abbrev branch (done : Nat → Prop) := Rule final reg interp (support done) (tests done)

theorem same_entries {e : Equation} (h : e ∈ inputState.equations) : e ∈ final.equations :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem now_return : returnRow ∈ final.equations :=
  List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
theorem now_child : childRow ∈ final.equations := List.mem_append_right _ List.mem_cons_self

theorem rejoined_old : Derives final (.variable 6) (.variable 5) :=
  .trans (.row now_return) (.symm (.row now_child))

theorem receipt : Receipt oldFinal final := by
  refine ⟨fun _ h => h,fun _ h => .interval h,?_⟩
  intro row h
  rcases List.mem_append.mp h with before|leaf
  · rcases List.mem_append.mp before with orig|output
    · exact .row (same_entries orig)
    · cases List.mem_singleton.mp output
      exact rejoined_old
  · cases List.mem_singleton.mp leaf
    exact .row now_child

theorem reverseReceipt : Receipt final oldFinal := by
  refine ⟨fun _ h => h,fun _ h => .interval h,?_⟩
  intro row h
  rcases List.mem_append.mp h with before|leaf
  · rcases List.mem_append.mp before with orig|output
    · exact .row (List.mem_append_left _ (List.mem_append_left _ orig))
    · cases List.mem_singleton.mp output
      exact .trans (.row (List.mem_append_left _ (List.mem_append_right _
        (show oldReturn ∈ [oldReturn] from List.mem_cons_self))))
        (.row (List.mem_append_right _ (show childRow ∈ [childRow] from List.mem_cons_self)))
  · cases List.mem_singleton.mp leaf
    exact .row (List.mem_append_right _ List.mem_cons_self)

theorem absent : oldReturn ∉ final.equations := by
  rw [table]
  simp only [oldRows,inputRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro (h|h|h|h|h|h|h|h|h|h)
  all_goals first | (solve | cases congrArg Equation.left h) | cases congrArg Equation.right h

theorem root_selected (done : Nat → Prop) : branch done root (.selected impl.id [child]) := by
  refine .selected (root_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩ ?_
    ⟨oldFinal,⟨frame⟩,receipt⟩
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases root_only d visible role
    exact wait (root_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [root_only d visible role]

theorem child_selected (done : Nat → Prop) : branch done child (.selected leaf.id []) := by
  refine .selected (child_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches done⟩ ?_
    ⟨oldFinal,⟨childFrame⟩,receipt⟩
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases child_only d visible role
    exact wait (child_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [child_only d visible role]

theorem tree (done : Nat → Prop) : Classify (branch done) root (.selected dict) :=
  ⟨.selected impl.id [.selected leaf.id []],
    .selected (root_selected done) (.cons (.selected (child_selected done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

theorem declared : Declared reg root := by
  intro out requested
  cases List.mem_singleton.mp requested
  exact ⟨none,rfl⟩

theorem every_model (m) (valid : Models final m) : Evidence reg interp m root dict :=
  dictionary checked coverage declared valid (tree (fun _ => False))

/-- Same protected logical targets and ordered children, without a literal root output row. -/
theorem accepted_without_literal :
    oldReturn ∉ final.equations ∧
      GeneralDeclarativeCompileLists321.Result final
        (GeneralDeclarativeNFComplete324.facts reg interp frame.capture impl root [child]) ∧
      Models final (GeneralDeclarativeArityModels330.assignment GeneralDeclarativeRepeat320.int) ∧
      Evidence reg interp (GeneralDeclarativeArityModels330.assignment GeneralDeclarativeRepeat320.int) root dict := by
  have model := relays_models reverseReceipt _ GeneralDeclarativeArityModels330.stable
  exact ⟨absent,(complete checked coverage List.mem_cons_self rfl declared frame receipt).1,
    model,every_model _ model⟩

end Yulang.GeneralDeclarativeCurrentResult330
