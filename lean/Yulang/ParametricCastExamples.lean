import Yulang.ParametricCasts

namespace Yulang.ParametricCasts.Examples

open Roles

def integer : Term := .app 0 []
def string : Term := .app 1 []
def box (element : Term) : Term := .app 10 [element]
def packet (element : Term) : Term := .app 11 [element]

def unboxRule : Rule := ⟨box (.var 0), .var 0⟩
def growRule : Rule := ⟨.var 0, box (.var 0)⟩
def duplicateRule : Rule := ⟨.app 12 [.var 0, .var 1], .app 13 [.var 0, .var 0]⟩
def escapingRule : Rule := ⟨.var 0, .var 1⟩

theorem unbox_checked : unboxRule.check = true := by decide
theorem growing_parametric_rule_rejected : growRule.check = false := by decide
theorem duplicated_variable_rejected : duplicateRule.check = false := by decide
theorem target_only_variable_rejected : escapingRule.check = false := by decide

theorem unbox_valid : Valid [unboxRule] :=
  (checkRules_exact _).mp (by decide)

theorem unbox_ground (term : Term) (ground : Ground term) : Ground (box term) := by
  simpa [Ground, box, Term.bound, argsBound] using ground

/-- The result instance can be any ground constructor tree, not merely nominal leaves. -/
theorem unbox_accepts_every_ground_instance (term : Term) (ground : Ground term) :
    query [unboxRule] (box term) term = some true := by
  apply (query_success_iff _ _ _).mpr
  refine ⟨unbox_valid, unbox_ground term ground, .step .refl ?_⟩
  exact ⟨unboxRule, by simp, fun _ => term, rfl, rfl⟩

theorem unbox_structured_result :
    query [unboxRule] (box (.app 20 [integer, string])) (.app 20 [integer, string]) = some true :=
  unbox_accepts_every_ground_instance _ (by decide)

theorem invalid_rule_rejected_before_search (source target : Term) :
    query [unboxRule, growRule] source target = none := by
  simp [query, checkRules, unbox_checked, growing_parametric_rule_rejected]

theorem non_ground_query_rejected (rules : List Rule) (name : Nat) (target : Term) :
    query rules (.var name) target = none := by
  simp [query, Ground, Term.bound]

/-- Fixed ground declarations are not incorrectly subjected to the parametric
nonincrease restriction. Their target contributes to the finite size bound. -/
def groundGrowth : Rule := ⟨integer, box integer⟩

theorem fixed_ground_growth_checked : groundGrowth.check = true := by decide

theorem fixed_ground_growth_searches :
    query [groundGrowth] integer (box integer) = some true := by
  apply (query_success_iff _ _ _).mpr
  refine ⟨(checkRules_exact _).mp (by decide), by decide, .step .refl ?_⟩
  exact ⟨groundGrowth, by simp, fun _ => integer, rfl, rfl⟩

def toPacket : Rule := ⟨box (.var 0), packet (.var 0)⟩
def toBox : Rule := ⟨packet (.var 0), box (.var 0)⟩
def parametricCycle : List Rule := [toPacket, toBox]

theorem equal_size_cycle_checked : checkRules parametricCycle = true := by decide

theorem cycle_forward_at_every_ground_instance (term : Term) (ground : Ground term) :
    query parametricCycle (box term) (packet term) = some true := by
  apply (query_success_iff _ _ _).mpr
  refine ⟨(checkRules_exact _).mp equal_size_cycle_checked,
    unbox_ground term ground, .step .refl ?_⟩
  exact ⟨toPacket, by simp [parametricCycle], fun _ => term, rfl, rfl⟩

/-- The declarative relation really contains the cycle; termination has not been
obtained by forbidding its second edge. -/
theorem equal_size_round_trip (term : Term) :
    Path parametricCycle (box term) (box term) := by
  apply Path.step (target := box term)
  · exact Path.step .refl
      ⟨toPacket, by simp [parametricCycle], fun _ => term, rfl, rfl⟩
  · exact ⟨toBox, by simp [parametricCycle], fun _ => term, rfl, rfl⟩

theorem cycle_cannot_invent_constructor :
    ¬ Path parametricCycle (box integer) (.app 99 []) := by
  intro path
  have supported := path_over parametricCycle
    ((checkRules_exact _).mp equal_size_cycle_checked) (by decide) path
  simp [Over, alphabet, parametricCycle, box, packet, integer, toPacket, toBox,
    symbols, argsSymbols] at supported

theorem impossible_cycle_target_rejected :
    query parametricCycle (box integer) (.app 99 []) = some false :=
  (query_failure_iff _ _ _).mpr
    ⟨(checkRules_exact _).mp equal_size_cycle_checked, by decide, cycle_cannot_invent_constructor⟩

def constantCycle : List Rule := [⟨integer, string⟩, ⟨string, integer⟩]

/-- Small executable regressions exercise the graph closure with both edges present. -/
theorem constant_cycle_search_computes : query constantCycle integer string = some true := by
  decide +kernel

theorem constant_cycle_missing_computes : query constantCycle integer (.app 99 []) = some false := by
  decide +kernel

end Yulang.ParametricCasts.Examples
