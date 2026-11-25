import Yulang.GeneralDeclarativeI65I74RepeatedCentersModel421

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)

private theorem not_unary {p} (a : Choice p) {c : Capture}
    (one : p.root.demand.arguments = [c]) : False := by
  have impossible := congrArg List.length (one.symm.trans a.originalArgs)
  simp at impossible

private theorem not_binary_candidates {p} (a : Choice p) {d f : GeneralDeclarations.Declaration}
    (two : visible p.state.core p.root = [d,f]) : False := by
  have impossible := congrArg List.length (two.symm.trans a.only)
  simp at impossible

private theorem not_one_output {p} (a : Choice p)
    (one : p.root.demand.outputs.length = 1) : False := by
  simp [a.noOutputs] at one

private theorem residual_arg_count421 {s q e}
    (r : ClosedResidual415.ResidualElection s q e) :
    ∃ c, q.demand.arguments = [c] := by
  cases r with
  | parent rows p => exact ⟨_,rows.requested⟩
  | leaf rows p child => exact ⟨_,rfl⟩

private theorem plain_arg_count421 {s q e}
    (r : PlainMerged416.PlainElection s q e) :
    ∃ c, q.demand.arguments = [c] := by
  cases r with
  | actual rows h => exact ⟨_,rows.requested⟩

private theorem rigid_candidates421 {s q e}
    (r : RigidRival418.ExactWinner s q e) :
    ∃ d f, visible s.core q = [d,f] := by
  cases r with
  | actual h =>
    rcases h.ordered with first|second
    · exact ⟨_,_,first⟩
    · exact ⟨_,_,second⟩

private theorem pick_output_count421 {s q e}
    (r : ExplicitPick419.PickElection s q e) : q.demand.outputs.length = 1 := by
  cases r with
  | actual h => exact h.single

private theorem default_output_count421 {s q e}
    (r : RoleDefault420.DefaultElection s q e) : q.demand.outputs.length = 1 := by
  cases r with
  | actual h => exact h.single

/-- An actual incompatible repeated head does not conflict with an old
successful local decision for the same State and Request. R0 would
require the very tie shown absent; each added R1–R12 selecting rule
would require one argument, two visible candidates, or one output.
Raw K2, other old diagnostics, and checker branches are not changed. -/
theorem existing_R12_selection_cannot_bypass_post_conflict421 {p} {a : Choice p}
    (bad : Conflict a) (e : Event p.state p.root) {needs} :
    ¬ RoleDefault420.R12.elected p.state p.root e needs := by
  rintro ((((((((base|named)|list)|whereList)|residual)|plain)|rigid)|pick)|default)
  · exact original_R0_selection_cannot_bypass_post_conflict421 bad e base
  · obtain ⟨read⟩ := named.2
    exact not_unary a read.test.asked
  · obtain ⟨read⟩ := list.2
    exact not_unary a read.test.asked
  · obtain ⟨read⟩ := whereList.2
    exact not_unary a read.test.asked
  · obtain ⟨read⟩ := residual.2
    obtain ⟨_,one⟩ := residual_arg_count421 read
    exact not_unary a one
  · obtain ⟨read⟩ := plain.2
    obtain ⟨_,one⟩ := plain_arg_count421 read
    exact not_unary a one
  · obtain ⟨read⟩ := rigid.2
    obtain ⟨_,_,two⟩ := rigid_candidates421 read
    exact not_binary_candidates a two
  · obtain ⟨read⟩ := pick.2
    exact not_one_output a (pick_output_count421 read)
  · obtain ⟨read⟩ := default.2
    exact not_one_output a (default_output_count421 read)

private theorem same_requested_tie421 {p} (a b : Choice p) : a.tie = b.tie := by
  have ordered := List.cons.inj (a.originalArgs.symm.trans b.originalArgs)
  have later := (List.cons.inj ordered.2).1
  simp [Choice.tie,ordered.1,later]

private theorem accepted_original_tie_present421 {s q e}
    (localRule : TiedElection s q e) (b : Choice ⟨s,q⟩) :
    b.tie ∈ s.core.current.ordinary.equations := by
  cases localRule with
  | actual positive =>
    rename_i a
    rw [← same_requested_tie421 a b]
    exact positive.retained

/-- The widened semantics cannot simultaneously select a dictionary
for the same incompatible request. This is a semantic statement about
any finite derivation, not only the result of running either checker. -/
theorem incompatible_request_selects_no_R13_dictionary421 {p} {a : Choice p}
    (bad : Conflict a) (d : CommonRoleOutermostResolver.Dictionary) :
    ¬ I72.Classifies R13 p.state p.root (.selected d) := by
  rintro ⟨_,_,⟨trace⟩,summary⟩
  cases trace with
  | rootK2 _ => cases summary
  | other verdict _ _ _ => cases verdict <;> cases summary
  | selected event _ read _ _ =>
    rcases read with old|⟨_,⟨new⟩⟩
    · exact existing_R12_selection_cannot_bypass_post_conflict421 bad event old
    · rcases p with ⟨s,q⟩
      exact bad.absent (accepted_original_tie_present421 new a)

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
