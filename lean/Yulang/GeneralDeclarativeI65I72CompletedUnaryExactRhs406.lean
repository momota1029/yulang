import Yulang.GeneralDeclarativeI65I72CompletedUnaryCompatibility406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (lookup lookup_exact)
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier (Equivalent)

/-- Fixed original occurrence means one body, one B6 source plan,
and one named typed tree, not just equal denoted values. -/
theorem named_B6_output_at_same_original_frame_unique406 {s : State} {q : Request}
    {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (checked : Checked (authoredRegistry s.core.current))
    (left right : NamedMixedOutput401 s.b6 f i) : left = right := by
  have declaration := checked.2 f.decl (List.mem_of_getElem? f.authored)
  cases left with
  | mk lb ls lp lt lr lf =>
    cases right with
    | mk rb rs rp rt rr rf =>
      have sourceL := (lookup_exact _ _ declaration.identified.2.2.1 _ _).mpr ls
      have sourceR := (lookup_exact _ _ declaration.identified.2.2.1 _ _).mpr rs
      have bodyEq : lb = rb := Option.some.inj (sourceL.symm.trans sourceR)
      subst rb
      have planEq : lp = rp := Option.some.inj (lt.symm.trans rt)
      subst rp
      have rhsEq : lr = rr := Option.some.inj (lf.symm.trans rf)
      subst rr
      rfl

theorem completed_B6_body_at_same_frame_is_unique406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} {payload : OriginalPayload406 chosen}
    (a b : CompletedBody406 payload) : a = b := by
  cases a with
  | mk first =>
    cases b with
    | mk second =>
      have same : first = second := funext fun i =>
        named_B6_output_at_same_original_frame_unique406 chosen.gate.checked (first i) (second i)
      rw [same]

/-- One originally installed emission suffices for every replay of
that same frame. Installation is not derived from syntax or typing. -/
theorem one_installed_body_suffices_for_exact_replay406 {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} {payload : OriginalPayload406 chosen}
    (known : ∃ body : CompletedBody406 payload, body.Fixed) :
    ∀ candidate : CompletedBody406 payload, candidate.Fixed := by
  obtain ⟨original,fixed⟩ := known
  intro candidate
  rw [completed_B6_body_at_same_frame_is_unique406 candidate original]
  exact fixed

/-- The native lower actually consumes this producer's literal B6
read at the given output ordinal, not just an ordinary row that
happens to have the same denotation. The actual equation in the
same model has the consumer's *fixed lower name* as target. -/
theorem completed_lower_replays_original_B6_occurrence406 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) (m : Model) (fit : Fits s m) :
    let producer := chosen.producer
    let out := producer.event.outputs chosen.need.ordinal
    out.receipt.occurrence = chosen.need.producer.occurrence ∧
    out.receipt.outputOrdinal = chosen.need.ordinal.val ∧
    s.b6.read chosen.need.producer producer.event.frame.ordinal chosen.need.ordinal out.body = some out.plan ∧
    out.receipt.original.target = chosen.gate.arg.lower ∧
    ∃ denotation, out.receipt.actualEquation m = some (chosen.gate.arg.lower,denotation) ∧
      evaluateMixedRhs401 (sourceRead401 m (producer.event.frame.slots out.body)) out.plan = some denotation ∧
      Equivalent (m.assignment chosen.gate.arg.lower).1 denotation := by
  let producer := chosen.producer
  let output := producer.event.outputs chosen.need.ordinal
  have target : output.receipt.original.target = chosen.gate.arg.lower :=
    (congrArg (fun r : NamedMixedReceipt401 s.core => r.original.target)
      producer.sameTypedOutput).trans chosen.gate.lowerTarget
  refine ⟨rfl,rfl,output.originalTyped,target,?_⟩
  obtain ⟨denotation,original,typed⟩ := named_mixed_output_is_fixed_equation401 output m
  have visibleCode := (actual_typed_point_yields_literal_declared_code404 chosen.need.expected.rhs chosen.gate.lowerTyped).2
  have sameCode := (congrArg (fun r : NamedMixedReceipt401 s.core => fixedValueCode403 r.rhs)
    producer.sameTypedOutput).trans visibleCode
  have eval := fixed_value_code_same_model403 output.rhs m _ sameCode
  have evaluated : output.receipt.actualEquation m = some (chosen.gate.arg.lower,
      value (environment m.assignment) .actual (.nominal chosen.gate.key [.variable chosen.gate.lowerPayload])) := by
    unfold NamedMixedReceipt401.actualEquation
    rw [target]
    change Option.map (fun v => (chosen.gate.arg.lower,v))
      (evaluateMixedRhs401 (actualNamedMixedRead401 m) output.rhs) = _
    rw [eval]
    rfl
  change output.receipt.actualEquation m = some (output.receipt.original.target,denotation) at original
  rw [target] at original
  have equal := (Prod.mk.inj (Option.some.inj (original.symm.trans evaluated))).2
  refine ⟨denotation,original,typed,?_⟩
  rw [equal]
  exact (completed_selected_endpoints_have_same_model406 chosen m fit).2.1

end Yulang.GeneralDeclarativeI65.I72
