import Yulang.ScopedCaseEvaluation
import Yulang.CaseCoverageSafety

/-!
# Coverage soundness with lexical pattern defaults

Coverage describes each default by a domain independent of the particular
runtime environment. The explicit `DefaultBounded` condition requires the
independently inferred default type, in every scope where it is used, to be
contained in that domain. Evaluation itself is justified by `DefaultSound`
in the current typed environment, never by assuming that a match succeeds.

The conservative structural coverage checker is reused without changing its
acceptance criteria. An additional payload-partition checker can reuse the
same matching witness.
-/

namespace Yulang.ScopedCaseCoverage

open CaseValues CasePatterns CaseCoverage LiteralValues EvaluationTrace
open ScopedCasePatterns (DefaultSound)

def DefaultBounded (DefaultTyped : List (Nat × Ty F) → D → Ty F → Prop)
    (domains : D → Domain) : Prop :=
  ∀ types code type, DefaultTyped types code type → Ty.Le type ((domains code).denote F)

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

private theorem total_has_cell (total : Total domains pattern input) (value : Value F)
    (valid : input.denote F value) :
    ∃ cell, Handles domains pattern cell ∧ cell.denote F value := by
  obtain ⟨cell, partition, valid⟩ := domain_has_cell input value valid
  exact ⟨cell, (total_iff _ _ _).mp total cell partition, valid⟩

private theorem andThen_matches (first : Observation F E R) (last : Bindings F → Observation F E R)
    (a : ∃ values, first.result = .ok (some values) ∧ BindingsHold left values)
    (b : ∀ values, BindingsHold left values →
      ∃ more, (last values).result = .ok (some more) ∧ BindingsHold right more) :
    ∃ values, (ScopedCasePatterns.andThen first last).result = .ok (some values) ∧
      BindingsHold (left ++ right) values := by
  obtain ⟨values, firstEval, firstValid⟩ := a
  obtain ⟨more, lastEval, lastValid⟩ := b values firstValid
  exact ⟨values ++ more,
    by simp [ScopedCasePatterns.andThen, Logged.bind_result, firstEval, lastEval, success, Logged.ofResult],
    firstValid.append lastValid⟩

/-- A covered, independently typed pattern succeeds in every matching typed
environment and input. The coverage domain and input type may differ; the
actual value must satisfy both. This permits checking individual payload
cells while typing an arm against the complete merged row. -/
theorem typing_total_matches (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (domains : D → Domain)
    (bounded : DefaultBounded DefaultTyped domains)
    (typed : ScopedCasePatterns.Typing DefaultTyped types pattern input bindings) :
    ∀ domain, Total domains pattern domain →
      ∀ (environment : Bindings F), BindingsHold types environment →
        ∀ (value : Value F), input value → domain.denote F value →
          ∃ matched, (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result =
            .ok (some matched) ∧ BindingsHold bindings matched := by
  induction typed with
  | wildcard => intro domain total environment valid value valueValid domainValid; exact ⟨[], rfl, .nil⟩
  | bind => intro domain total environment valid value valueValid domainValid; exact ⟨_, rfl, .cons valueValid .nil⟩
  | literal admissible =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | literal matched =>
          cases matched <;> change value = _ at holds <;> subst value <;>
            exact ⟨[], by simp [ScopedCasePatterns.run, matchCheck, success, Logged.ofResult], .nil⟩
  | intRange admissible bounds =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | intRange matched =>
          cases matched with
          | @int integer _ bounds =>
              change value = .literal (.int integer) at holds
              subst value
              have checked := (intRangeCheck_exact (FloatValue := F) _ _ (.int integer)).mpr (.int bounds)
              exact ⟨[], by simp [ScopedCasePatterns.run, checked, success, Logged.ofResult], .nil⟩
  | pair left right leftIH rightIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | pair first last =>
          cases value with
          | pair a b =>
              exact andThen_matches _ _ (leftIH _ first environment valid a valueValid.1 holds.1)
                (fun prior priorValid => rightIH _ last (prior ++ environment) (priorValid.append valid)
                  b valueValid.2 holds.2)
          | _ => cases valueValid
  | recordEnd =>
      intro domain total environment valid value valueValid domainValid
      cases value with
      | record fields => exact ⟨[], rfl, .nil⟩
      | _ => cases valueValid
  | field admissible child rest childIH restIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | field selected head tail =>
          have itemType := admissible value valueValid
          have itemDomain := selected.values value holds
          cases value with
          | record fields =>
              obtain ⟨item, found, itemValid⟩ := itemType
              obtain ⟨sameItem, sameFound, domainValid⟩ := itemDomain
              have same : sameItem = item := Option.some.inj (sameFound.symm.trans found)
              subst sameItem
              simp only [ScopedCasePatterns.run, found]
              exact andThen_matches _ _ (childIH _ head environment valid item itemValid domainValid)
                (fun prior priorValid => restIH _ tail (prior ++ environment) (priorValid.append valid)
                  (.record fields) valueValid holds)
          | _ => cases itemType
  | defaultField admissible fallbackTyped child rest childIH restIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | defaultField selected head tail =>
          have itemType := admissible value valueValid
          have itemDomain := selected.values value holds
          cases value with
          | record fields =>
              cases found : lookup _ fields with
              | some item =>
                  rw [ScopedCasePatterns.default_present _ _ _ _ _ _ _ _ _ found]
                  exact andThen_matches _ _
                    (childIH _ head environment valid item (.inl (itemType item found)) (.inl (itemDomain item found)))
                    (fun prior priorValid => restIH _ tail (prior ++ environment) (priorValid.append valid)
                      (.record fields) valueValid holds)
              | none =>
                  obtain ⟨item, evaluated, itemValid⟩ := defaults _ _ _ fallbackTyped environment valid
                  rw [ScopedCasePatterns.default_absent _ _ _ _ _ _ _ _ found, Logged.bind_result, evaluated]
                  exact andThen_matches _ _
                    (childIH _ head environment valid item (.inr itemValid)
                      (.inr (bounded _ _ _ fallbackTyped item itemValid)))
                    (fun prior priorValid => restIH _ tail (prior ++ environment) (priorValid.append valid)
                      (.record fields) valueValid holds)
          | _ => cases itemType
  | nil =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled
      change value = .list [] at holds
      subst value
      exact ⟨[], rfl, .nil⟩
  | cons head rest headIH restIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | cons first tail =>
          cases value with
          | list values =>
              cases values with
              | nil => cases holds
              | cons a more =>
                  exact andThen_matches _ _
                    (headIH _ first environment valid a (valueValid a (by simp)) holds.1)
                    (fun prior priorValid => restIH _ tail (prior ++ environment) (priorValid.append valid)
                      (.list more) (fun item member => valueValid item (by simp [member])) holds.2)
          | _ => cases valueValid
  | snoc init last initIH lastIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | snoc first tail =>
          cases value with
          | list values =>
              cases values with
              | nil => cases holds
              | cons a more =>
                  simp only [ScopedCasePatterns.run]
                  cases reversed : (a :: more).reverse with
                  | nil => simp at reversed
                  | cons final earlier =>
                      have original : a :: more = earlier.reverse ++ [final] := by
                        have same := congrArg List.reverse reversed
                        simpa using same
                      refine andThen_matches _ _ (initIH _ first environment valid (.list earlier.reverse) ?_
                        (fun _ _ => trivial)) ?_
                      · intro item member
                        apply valueValid item
                        rw [original]
                        simp [member]
                      · intro prior priorValid
                        apply lastIH _ tail (prior ++ environment) (priorValid.append valid) final ?_ trivial
                        apply valueValid final
                        rw [original]
                        simp
          | _ => cases valueValid
  | variant child childIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | variant payload =>
          cases value with
          | variant name item =>
              obtain ⟨rfl, itemValid⟩ := valueValid
              simpa [ScopedCasePatterns.run] using childIH _ payload environment valid item itemValid holds.2
          | _ => cases valueValid
  | @mergedVariant tag payload types p bindings row found child childIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | variant payloadTotal =>
          cases value with
          | variant name item =>
              obtain ⟨rfl, domainValid⟩ := holds
              obtain ⟨actual, actualFound, itemValid⟩ := valueValid
              have equal : actual = payload := Option.some.inj (actualFound.symm.trans found)
              subst actual
              simpa [ScopedCasePatterns.run] using
                childIH _ payloadTotal environment valid item itemValid domainValid
          | _ => cases valueValid
  | nominal child childIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | nominal payload =>
          cases value with
          | nominal name ctor item =>
              obtain ⟨rfl, rfl, itemValid⟩ := valueValid
              simpa [ScopedCasePatterns.run] using childIH _ payload environment valid item itemValid holds.2.2
          | _ => cases valueValid
  | @mergedNominal ctorId payload types p bindings typeId row found child childIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | nominal payloadTotal =>
          cases value with
          | nominal typeName ctorName item =>
              obtain ⟨rfl, rfl, domainValid⟩ := holds
              obtain ⟨_, actual, actualFound, itemValid⟩ := valueValid
              have equal : actual = payload := Option.some.inj (actualFound.symm.trans found)
              subst actual
              simpa [ScopedCasePatterns.run] using
                childIH _ payloadTotal environment valid item itemValid domainValid
          | _ => cases valueValid
  | @or types p input bindings q left right leftIH rightIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | orLeft first =>
          obtain ⟨matched, evaluated, bindingsValid⟩ := leftIH _ first environment valid value valueValid holds
          exact ⟨matched, by simp [ScopedCasePatterns.run, Logged.bind_result, evaluated, success, Logged.ofResult],
            bindingsValid⟩
      | orRight last =>
          obtain ⟨rightMatched, rightEval, rightValid⟩ := rightIH _ last environment valid value valueValid holds
          have safe := ScopedCasePatterns.typing_matches floatCheck defaultEval defaults left
            environment valid value valueValid
          cases observed : (ScopedCasePatterns.run floatCheck defaultEval environment p value).result with
          | error error => rw [observed] at safe; cases safe
          | ok result =>
              cases result with
              | none => exact ⟨rightMatched, by simp [ScopedCasePatterns.run, Logged.bind_result, observed, rightEval],
                  rightValid⟩
              | some matched => exact ⟨matched,
                  by simp [ScopedCasePatterns.run, Logged.bind_result, observed, success, Logged.ofResult],
                  by simpa [observed, Holds] using safe⟩
  | as child childIH =>
      intro domain total environment valid value valueValid domainValid
      obtain ⟨cell, handled, holds⟩ := total_has_cell total value domainValid
      cases handled with
      | as inner =>
          obtain ⟨matched, evaluated, bindingsValid⟩ := childIH _ inner environment valid value valueValid holds
          exact ⟨_ , by simp [ScopedCasePatterns.run, Logged.bind_result, evaluated, success, Logged.ofResult],
            .cons valueValid bindingsValid⟩
  | narrow below child childIH =>
      intro domain total environment valid value valueValid domainValid
      exact childIH domain total environment valid value (below value valueValid) domainValid

/-- A successful coverage check supplies a matching arm in the original
ordered arm list. The guard is absent, and bindings are evaluated using the
same scope as every preceding pattern component. -/
theorem covered_arms_match (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (domains : D → Domain)
    (bounded : DefaultBounded DefaultTyped domains)
    (arms : List (CaseEvaluation.Arm F D G B))
    (typed : ∀ arm ∈ arms,
      ∃ bindings, ScopedCasePatterns.Typing DefaultTyped types arm.pattern input bindings)
    (domain : Domain) (coverage : Covered domains (coverageArms arms) domain)
    (environment : Bindings F) (valid : BindingsHold types environment)
    (value : Value F) (valueValid : input value) (domainValid : domain.denote F value) :
    ∃ arm ∈ arms, arm.guard = none ∧
      ∃ matched, (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result =
        .ok (some matched) := by
  obtain ⟨cell, partition, cellValid⟩ := domain_has_cell domain value domainValid
  obtain ⟨projected, member, unguarded, total⟩ := (covered_iff _ _ _).mp coverage cell partition
  obtain ⟨arm, armMember, same⟩ := List.mem_map.mp member
  subst projected
  obtain ⟨bindings, armTyped⟩ := typed arm armMember
  obtain ⟨matched, evaluated, _⟩ := typing_total_matches floatCheck defaultEval defaults domains bounded
    armTyped cell total environment valid value valueValid cellValid
  exact ⟨arm, armMember, by simpa using unguarded, matched, evaluated⟩

theorem checked_arms_evaluate (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged (CaseEvaluation.Event E) R (Value F))
    (environment : Bindings F)
    (guardEval : G → Bindings F → Logged (CaseEvaluation.Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (CaseEvaluation.Event E) R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (domains : D → Domain)
    (bounded : DefaultBounded DefaultTyped domains)
    (guards : CaseEvaluation.GuardSound GuardTyped guardEval)
    (bodies : CaseEvaluation.BodySound BodyTyped bodyEval)
    (arms : List (CaseEvaluation.Arm F D G B))
    (typed : ∀ arm ∈ arms,
      ScopedCaseEvaluation.ArmTyping DefaultTyped GuardTyped BodyTyped types arm input target)
    (domain : Domain) (checked : check domains (coverageArms arms) domain = true)
    (valid : BindingsHold types environment)
    (value : Value F) (valueValid : input value) (domainValid : domain.denote F value) (index : Nat) :
    ∃ result, (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval
      value index arms).result = .ok (some result) ∧ target result := by
  have patternTyped : ∀ arm ∈ arms,
      ∃ bindings, ScopedCasePatterns.Typing DefaultTyped types arm.pattern input bindings := by
    intro arm member
    cases typed arm member with
    | arm pattern _ _ => exact ⟨_, pattern⟩
  have matching := covered_arms_match floatCheck defaultEval defaults domains bounded arms patternTyped
    domain ((check_exact _ _ _).mp checked) environment valid value valueValid domainValid
  exact ScopedCaseEvaluation.runArms_progress floatCheck defaultEval environment guardEval bodyEval
    defaults guards bodies arms typed value valueValid matching index valid

end Yulang.ScopedCaseCoverage
