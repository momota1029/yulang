import Yulang.GeneralDeclarativeLateProvider326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeLateWithProvider326
open GeneralDeclarativeLateProviderDecl326
open GeneralDeclarativeLateProvider326 (branch tests safe completed earlier_complete)
open GeneralDeclarativePairDecl326 (root child impl rootArg leftArg normalCode)
open GeneralDeclarativeCovariantState326 (final root_range left_range center parentRow childRow)
open GeneralDeclarativeCovariantSupport326 (controlled lower upper child_ready_iff child_waits)
open GeneralDeclarativeCovariantFrame326 (parentBase leafBase placement child_exact)
open GeneralDeclarativeCovariantLate326 (parent_ready)
open GeneralDeclarativeProjectedFrame326 (Frame sound)
open GeneralDeclarativeLowerKnown321 (ready_iff_not_delayed)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputSource323 (Declared)
open CommonRoleOutermostResolver (Classify Dictionary)

abbrev dictionary : Dictionary := .node impl.id [.node leaf.id []]

theorem parent_probe (done : Nat → Prop) :
    HeadMatches (restriction (controlled done)) constructors interpretation root impl :=
  .cons ⟨root_range,normalCode,_,_,rfl,lower done,upper done⟩ .nil

theorem leaf_probe (done : Nat → Prop) :
    HeadMatches (restriction (controlled done)) constructors interpretation child leaf :=
  .cons ⟨left_range,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,4⟩],rfl,.capture,.capture⟩ .nil

theorem parent_frame (done : Nat → Prop) : Frame final reg interpretation (controlled done) root impl parentBase placement := by
  have prior := GeneralDeclarativeCovariantFrame326.parent_frame done
  refine ⟨.cons ⟨root_range,.projected rfl center .capture .capture ?_⟩ .nil,
    prior.ranges,?_,[parentRow],rfl,fun _ present => List.mem_append_left _ (List.mem_append_right _ present)⟩
  · intro o mentions
    rcases List.mem_cons.mp mentions with rfl|more
    · exact .refl _
    · cases List.mem_singleton.mp more
      exact .refl _
  · intro cl present
    cases List.mem_singleton.mp present
    constructor
    · refine ⟨[.variable 0],rfl,?_⟩
      intro n p e index _ no
      cases List.mem_singleton.mp (List.mem_of_getElem? index)
      exact False.elim (no 0 rfl)
    · intro eq named
      cases List.mem_singleton.mp named
      exact ⟨.variable 2,rfl,fun need => False.elim (need ⟨2,rfl,List.mem_cons_self⟩)⟩

theorem leaf_frame (done : Nat → Prop) : Frame final reg interpretation (controlled done) child leaf leafBase placement := by
  refine ⟨.cons ⟨left_range,.ordinary (.actual rfl .capture ?_)⟩ .nil,fun _ _ => left_range,
    fun _ never => False.elim (List.not_mem_nil never),[childRow],rfl,fun _ h => List.mem_append_right _ h⟩
  intro o found
  cases List.mem_singleton.mp found
  exact .refl _

theorem root_only (d) (visible : d ∈ reg.declarations) (role : d.role = root.role) : d = impl := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with h|h|h
  · exact h
  · cases h
    cases role
  · cases h
    cases role

theorem child_only (d) (visible : d ∈ reg.declarations) (role : d.role = child.role) : d = leaf := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with h|h|h
  · cases h
    cases role
  · exact h
  · cases h
    cases role

theorem root_choice (done : Nat → Prop) : branch done root (.selected impl.id [child]) := by
  refine .selected (parent_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,parent_probe done⟩ ?_
    ⟨parentBase,placement,parent_frame done,child_exact⟩
  · rintro ⟨d,⟨visible,role⟩,blocked⟩
    cases root_only d visible role
    exact blocked (parent_probe done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [root_only d visible role]

theorem child_wait (done : Nat → Prop) (absent : ¬done 42) : branch done child .pending := by
  refine GeneralDeclarativePriority321.Local.unsupported ?_ (safe done _)
  apply Classical.byContradiction
  intro no
  exact child_waits done absent ((ready_iff_not_delayed (controlled done) child).mpr no)

theorem child_choice (done : Nat → Prop) (found : done 42) : branch done child (.selected leaf.id []) := by
  refine .selected ((child_ready_iff done).mpr found) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,leaf_probe done⟩ ?_
    ⟨leafBase,placement,leaf_frame done,rfl⟩
  · rintro ⟨d,⟨visible,role⟩,blocked⟩
    cases child_only d visible role
    exact blocked (leaf_probe done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [child_only d visible role]

theorem before : Classify (branch (fun _ => False)) root .pending :=
  ⟨.selected impl.id [.pending],.selected (root_choice _) (.cons (.pending (child_wait _ id)) .nil),
    .selected (.cons .pending .nil) (.pending (by simp) (by simp) (by simp))⟩

theorem after : Classify (branch completed) root (.selected dictionary) :=
  ⟨.selected impl.id [.selected leaf.id []],
    .selected (root_choice _) (.cons (.selected (child_choice _ earlier_complete) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

/-- The transition of the actual covariant tree is triggered by a
verified diagnostic from a distinct checked provider in the same
registry. The provider did not assume its own output was usable. -/
theorem certified_transition (m) (model : Models final m) :
    Classify (branch (fun _ => False)) root .pending ∧
    (completed 42 ∧ Evidence reg interpretation m call GeneralDeclarativeLateProvider326.dict) ∧
    Classify (branch completed) root (.selected dictionary) ∧ Evidence reg interpretation m root dictionary := by
  refine ⟨before,⟨earlier_complete,GeneralDeclarativeLateProvider326.certified m model⟩,after,
    sound checked ?_ model after⟩
  intro out mentioned
  cases List.mem_singleton.mp mentioned
  exact ⟨none,rfl⟩

end Yulang.GeneralDeclarativeLateWithProvider326
