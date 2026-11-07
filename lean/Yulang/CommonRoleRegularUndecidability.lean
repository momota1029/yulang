import Yulang.CommonRoleRegularHalting
import Yulang.CommonRoleRegularWire

/-!
# No total effective resolver for the checked regular registry family

The input is an explicit finite serialization of actual declarations,
associated bodies, finite role signatures and a determined regular goal.
The quantified machine is a standard finite transition table over binary
tapes. No Boolean function on arbitrary semantic Common values is assumed.
The contract asks only for the success bit; any effective total exact resolver
returning status and a finite dictionary must in particular decide this bit.
-/

namespace Yulang.CommonRoleRegularUndecidability

open CommonRoleComputation (Tree Code Eval IsNode Halts)
open CommonRoleTuringBridge (Machine Runs encodeBool)
open CommonRoleTuringDelimited (initial classifierCode classifier_of_runs)
open CommonRoleRegularWire (descriptor queryWire queryCode eval_queryCode)
open CommonRoleRegularRegistry (registry)
open CommonRoleRegularHalting (goal)

/-- A deliberately weaker necessary condition of a total exact resolver:
on every query in the concrete checked family, halt and report whether
independent finite Common evidence is resolved without ambiguity. -/
def TotalRegularRoleClassifier (machine : Machine) : Prop :=
  ∀ code input, ∃ final,
    Runs machine (initial (queryWire code input)) final ∧
      (final.current = true ↔ CommonRoleLinearEvidence.Resolves (registry code) 0 (goal code input))

theorem no_total_regular_role_classifier :
    ¬ ∃ machine : Machine, TotalRegularRoleClassifier machine := by
  rintro ⟨machine, classifies⟩
  apply CommonRoleComputation.no_halting_classifier descriptor
  refine ⟨.seq queryCode (classifierCode machine), ?_⟩
  intro code input
  obtain ⟨final, executed, correct⟩ := classifies code input
  have halting : final.current = true ↔ Halts code input :=
    correct.trans (CommonRoleRegularHalting.resolves_exact code input)
  refine ⟨encodeBool final.current,
    .seq (eval_queryCode code input) (classifier_of_runs machine _ final executed), ?_⟩
  cases symbol : final.current <;>
    simpa only [symbol, encodeBool, CommonRoleTuringBridge.truth, IsNode,
      Bool.false_eq_true] using halting

/-- The same negative result stated with complete finite dictionaries,
not merely role-head observations. The dictionary retains actual Impl IDs
and every recursive where child in the existing Plan format. -/
def TotalRegularDictionaryClassifier (machine : Machine) : Prop :=
  ∀ code input, ∃ final,
    Runs machine (initial (queryWire code input)) final ∧
      (final.current = true ↔
        Nonempty (CommonRoleLinearEvidence.Dictionary (registry code) 0 (goal code input)))

theorem no_total_regular_dictionary_classifier :
    ¬ ∃ machine : Machine, TotalRegularDictionaryClassifier machine := by
  rintro ⟨machine, classifies⟩
  apply no_total_regular_role_classifier
  refine ⟨machine, ?_⟩
  intro code input
  obtain ⟨final, executed, correct⟩ := classifies code input
  exact ⟨final, executed, correct.trans ((CommonRoleRegularHalting.dictionary_exact code input).trans
    (CommonRoleRegularHalting.resolves_exact code input).symm)⟩

end Yulang.CommonRoleRegularUndecidability
