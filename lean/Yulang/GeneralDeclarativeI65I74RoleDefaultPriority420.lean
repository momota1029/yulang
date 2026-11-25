import Yulang.GeneralDeclarativeI65I74RoleDefaultMeaning420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open ExplicitPick419 (pickSyntax exactlyOneOutput)
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open Checker408 (Problem Result)

private theorem pick_not_variable_family420 {p} (a : DefaultPacket p)
    (scope : (d : Declaration) → d ∈ visible p.state.core p.root → RepeatedRow403 p.root d) : False := by
  let d := a.declaration.decl
  have seen : d ∈ visible p.state.core p.root := by simp [d,a.declaration.theOnlyOne]
  have stated : pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder ∈ d.head :=
    by simp [d,a.declaration.literal]
  rw [(scope d seen).literal] at stated
  obtain ⟨_,_,bad⟩ := List.mem_map.mp stated
  cases bad

private theorem pick_not_nominal420 {p} (a : DefaultPacket p)
    {d : Declaration} (seen : d ∈ visible p.state.core p.root) {literal : Pattern}
    (src : d.head = [literal]) {head args} (shape : normalize literal = .app head args) :
    False := by
  have ident : d = a.declaration.decl := by simpa [a.declaration.theOnlyOne] using seen
  have same := (List.cons.inj (src.symm.trans
    ((congrArg Declaration.head ident).trans a.declaration.literal))).1
  rw [same] at shape
  cases shape

private theorem pick_not_repeated_diagnostic420 {p v} (a : DefaultPacket p)
    (old : RepeatedOther403 p.state p.root v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨scope⟩ := scope
    exact pick_not_variable_family420 a scope.allVisible

private theorem pick_not_native_diagnostic420 {p v needs} (a : DefaultPacket p)
    (old : variableWithNativeK2403.other p.state p.root v needs) : False := by
  rcases old.2 with repeats|⟨_,_,view,_⟩
  · exact pick_not_repeated_diagnostic420 a repeats
  · exact pick_not_nominal420 a view.visibleRow view.exactHead view.dispatch

private theorem pick_not_completed_native_diagnostic420 {p v needs} (a : DefaultPacket p)
    (old : completedNativePrioritySource404.other p.state p.root v needs) : False := by
  rcases old with earlier|⟨_,⟨caller⟩⟩
  · exact pick_not_native_diagnostic420 a earlier
  · exact pick_not_nominal420 a caller.entry.visibleRow caller.entry.exactHead caller.entry.dispatch

private theorem pick_not_completed_choice_diagnostic420 {p v needs} (a : DefaultPacket p)
    (old : completedChoiceSource404.other p.state p.root v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact pick_not_completed_native_diagnostic420 a earlier
  · exact pick_not_variable_family420 a scope.allVisible

private theorem pick_has_output420 {p} (a : DefaultPacket p) (empty : p.root.demand.outputs = []) : False := by
  have h := a.single
  rw [empty] at h
  cases h

theorem no_older_diagnostic_claims_this_actual_Default420 {p verdict needs} (a : DefaultPacket p) :
    ¬ RigidRival418.R10.other p.state p.root verdict needs := by
  rintro ((((⟨_,family,old⟩|⟨_,_,⟨closed⟩⟩)|mixed)|opened)|⟨_,_,⟨ambiguity⟩⟩)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨scope⟩ := scope
        let d := a.declaration.decl
        have seen : d ∈ visible p.state.core p.root := by simp [d,a.declaration.theOnlyOne]
        have stated : pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder ∈ d.head :=
          by simp [d,a.declaration.literal]
        rw [(scope.allVisible d seen).literal] at stated
        obtain ⟨_,_,bad⟩ := List.mem_map.mp stated
        cases bad
    | repeated | whereTree => exact pick_not_repeated_diagnostic420 a old.2
    | nativeK2 | supported => exact pick_not_native_diagnostic420 a old
    | supportedK2 => exact pick_not_completed_native_diagnostic420 a old
    | supportedAmbiguity | authoredNative => exact pick_not_completed_choice_diagnostic420 a old
  · exact pick_has_output420 a closed.field.noOutputs
  · obtain ⟨_,_,⟨mixed⟩⟩ := mixed
    have count := mixed.rivalsExist
    simp [a.declaration.theOnlyOne] at count
  · obtain ⟨_,_,⟨view⟩⟩ := opened
    exact pick_has_output420 a view.input.noOutputs
  · have count := congrArg List.length a.declaration.theOnlyOne
    rcases ambiguity.ordered with h|h <;> simp [h] at count

private theorem one_requested_name_conflict420 {p} (a : DefaultPacket p)
    (b : ExplicitPick419.PickPacket p) : False := by
  have same := (List.cons.inj (b.declaration.theOnlyOne.symm.trans a.declaration.theOnlyOne)).1
  have member : b.declaration.explicit ∈ a.declaration.decl.associated := by
    rw [← same,b.declaration.exactlyWritten]
    exact List.mem_singleton_self _
  have indices : exactlyOneOutput p b.single = exactlyOneOutput p a.single :=
    Fin.ext rfl
  have supplied := b.retained.output.supplied
  rw [b.actualBody] at supplied
  cases supplied with
  | explicit _ _ equalName =>
    apply (original_default_requires_no_matching_explicit_equation420 a).1 _ member
    exact equalName.trans (congrArg (fun i => p.root.demand.outputs[i].name) indices)

private theorem prior_residual_demand_has_no_outputs420 {s q event}
    (d : ClosedResidual415.ResidualElection s q event) : q.demand.outputs = [] := by
  cases d with
  | parent rows _ => exact rows.noOutputs
  | leaf _ _ _ => rfl

/-- Non-default branches cannot also choose this original defaulted
request. The C419 explicitly written body case is excluded by *exact
associated-name* provenance, not by denying all explicit equations. -/
theorem no_prior_election_claims_the_defaulted_source420 {p needs}
    (a : DefaultPacket p) (event : Event p.state p.root) :
    ¬ ExplicitPick419.R11.elected p.state p.root event needs := by
  rcases p with ⟨s,q⟩
  have seen := event.frame.inScope
  have same : event.frame.decl = a.declaration.decl := by simpa [a.declaration.theOnlyOne] using seen
  have shape : event.frame.decl.head =
      [pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder] :=
    (congrArg Declaration.head same).trans a.declaration.literal
  have wrote : pickSyntax a.rows.x a.declaration.fieldBinder a.declaration.tailBinder ∈
      event.frame.decl.head := by simp [shape]
  rintro (((((((legacy|named)|list)|whereList)|record)|plain)|rival)|current)
  · rcases R0_selection_uses_independent_original_rule407 event legacy with allVariables|native
    · obtain ⟨_,bad,_⟩ := allVariables.2 event.frame.decl event.frame.inScope _ wrote
      cases bad
    · obtain ⟨fromSyntax⟩ := native
      have clash := (List.cons.inj (shape.symm.trans fromSyntax.test.writtenHead)).1
      cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := named
    have clash := (List.cons.inj (shape.symm.trans candidate.test.named)).1
    cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := list
    have clash := (List.cons.inj (shape.symm.trans candidate.test.named)).1
    cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := whereList
    have clash := (List.cons.inj (shape.symm.trans candidate.test.named)).1
    cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := record
    exact pick_has_output420 a (prior_residual_demand_has_no_outputs420 candidate)
  · obtain ⟨_,⟨candidate⟩⟩ := plain
    cases candidate with
    | actual _ old =>
      have clash := (List.cons.inj (shape.symm.trans old.head)).1
      cases clash
  · obtain ⟨_,⟨candidate⟩⟩ := rival
    cases candidate with
    | actual winner =>
      have impossible := congrArg List.length a.declaration.theOnlyOne
      rcases winner.ordered with h|h <;> simp [h] at impossible
  · obtain ⟨_,⟨candidate⟩⟩ := current
    cases candidate with
    | actual b => exact one_requested_name_conflict420 a b

theorem previous_checker_is_disjoint_on_actual_default420 (p : Problem) (r : Result)
    (a : DefaultPacket p) (w : ExplicitPick419.Witness) : ExplicitPick419.check p r w = false := by
  cases yes : ExplicitPick419.check p r w with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨e,trace,_,_⟩ := (ExplicitPick419.check_sound p r w yes).1
    generalize r.tree = tree at trace
    cases trace with
    | rootK2 cycle => exact a.rawSafe cycle
    | other _ _ src _ => exact no_older_diagnostic_claims_this_actual_Default420 a src
    | selected event _ src _ _ => exact no_prior_election_claims_the_defaulted_source420 a event src

/-- Even a well-typed available default plan does not replace an
unavailable or ill-typed explicit one with the same requested name. -/
theorem actual_same_name_equation_blocks_default_checker420 {p : Problem} {r : Result}
    {w : DefaultWire} {d : Declaration} {eq : GeneralDeclarations.Equation}
    (eligible : d ∈ visible p.state.core p.root) (member : eq ∈ d.associated)
    (name : ∀ i : Fin p.root.demand.outputs.length, eq.name = p.root.demand.outputs[i].name) :
    check p r (.roleDefault w) = false := by
  cases yes : check p r (.roleDefault w) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨a,_,notExplicit⟩ := successful_default_cannot_override_actual_explicit420 yes
    have same : d = a.declaration.decl := by simpa [a.declaration.theOnlyOne] using eligible
    exact notExplicit ⟨eq,same ▸ member,name (exactlyOneOutput p a.single)⟩

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
