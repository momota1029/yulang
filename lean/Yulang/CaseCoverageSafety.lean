import Yulang.CaseCoverage
import Yulang.CaseEvaluation

/-!
# Every covered input selects an unguarded matching arm

The only runtime premise concerns typed evaluation of default-expression
leaves. It is not a premise that a pattern or arm already succeeds. The float
comparator is arbitrary: the coverage rules never rely on float reflexivity.
This file supplies the matching witness needed by the ordered case evaluator.
-/

namespace Yulang.CaseCoverage

open CaseValues CasePatterns LiteralValues EvaluationTrace

/-- Only syntactically used default code needs a successful typed evaluation.
This remains usable when `D` is a raw expression type containing ill-typed code. -/
def DefaultsSoundFor (defaults : D → Domain) (defaultEval : D → Logged E R (Value F))
    (codes : List D) : Prop :=
  ∀ code ∈ codes, ∃ value, (defaultEval code).result = .ok value ∧ (defaults code).denote F value

theorem DefaultsSoundFor.left (sound : DefaultsSoundFor defaults defaultEval (first ++ last)) :
    DefaultsSoundFor defaults defaultEval first :=
  fun code member => sound code (List.mem_append_left last member)

theorem DefaultsSoundFor.right (sound : DefaultsSoundFor defaults defaultEval (first ++ last)) :
    DefaultsSoundFor defaults defaultEval last :=
  fun code member => sound code (List.mem_append_right first member)

theorem DefaultsSoundFor.tail (sound : DefaultsSoundFor defaults defaultEval (head :: rest)) :
    DefaultsSoundFor defaults defaultEval rest :=
  fun code member => sound code (List.mem_cons_of_mem head member)

theorem DefaultsSoundFor.arm {arms : List (Arm F D)} {arm : Arm F D}
    (sound : DefaultsSoundFor defaults defaultEval (armDefaults arms))
    (member : arm ∈ arms) : DefaultsSoundFor defaults defaultEval (patternDefaults arm.pattern) :=
  fun code used => sound code (List.mem_flatMap.mpr ⟨arm, member, used⟩)

private def NoError (result : Except R A) : Prop := ∃ value, result = .ok value

private theorem andThen_no_error (first : Observation F E R) (last : Unit → Observation F E R)
    (a : NoError first.result) (b : NoError (last ()).result) :
    NoError (andThen first last).result := by
  obtain ⟨left, ranLeft⟩ := a
  obtain ⟨right, ranRight⟩ := b
  cases left with
  | none => exact ⟨none, by simp [andThen, Logged.bind_result, ranLeft, Except.bind, miss, Logged.ofResult]⟩
  | some values =>
      cases right with
      | none => exact ⟨none, by simp [andThen, Logged.bind_result, ranLeft, ranRight, Except.bind, miss, Logged.ofResult]⟩
      | some more => exact ⟨some (values ++ more), by
          simp [andThen, Logged.bind_result, ranLeft, ranRight, Except.bind, success, Logged.ofResult]⟩

private theorem andThen_matches (first : Observation F E R) (last : Unit → Observation F E R)
    (a : ∃ bindings, first.result = .ok (some bindings))
    (b : ∃ bindings, (last ()).result = .ok (some bindings)) :
    ∃ bindings, (andThen first last).result = .ok (some bindings) := by
  obtain ⟨left, ranLeft⟩ := a
  obtain ⟨right, ranRight⟩ := b
  exact ⟨left ++ right, by simp [andThen, Logged.bind_result, ranLeft, ranRight,
    Except.bind, success, Logged.ofResult]⟩

/-- Every pattern is a terminating match-or-miss computation when each
invoked default leaf succeeds. This says nothing about coverage. -/
private theorem run_no_error (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (defaults : D → Domain)
    (pattern : Pattern F D) (value : Value F)
    (sound : DefaultsSoundFor defaults defaultEval (patternDefaults pattern)) :
    NoError (CasePatterns.run floatCheck defaultEval pattern value).result := by
  induction pattern generalizing value with
  | wildcard | bind => exact ⟨_, rfl⟩
  | literal expected =>
      cases value <;> simp only [CasePatterns.run]
      all_goals first
        | (split <;> exact ⟨_, rfl⟩)
        | exact ⟨_, rfl⟩
  | intRange lower upper =>
      cases value <;> simp only [CasePatterns.run]
      all_goals first
        | (split <;> exact ⟨_, rfl⟩)
        | exact ⟨_, rfl⟩
  | pair p q ihp ihq =>
      cases value <;> simp only [CasePatterns.run]
      all_goals first
        | exact andThen_no_error _ _ (ihp _ sound.left) (ihq _ sound.right)
        | exact ⟨_, rfl⟩
  | recordEnd => cases value <;> exact ⟨_, rfl⟩
  | field name p rest ihp ihr =>
      cases value with
      | record fields =>
          simp only [CasePatterns.run]
          cases found : lookup name fields with
          | none => exact ⟨_, rfl⟩
          | some item => exact andThen_no_error _ _ (ihp item sound.left) (ihr (.record fields) sound.right)
      | _ => exact ⟨_, rfl⟩
  | defaultField name fallback p rest ihp ihr =>
      cases value with
      | record fields =>
          cases found : lookup name fields with
          | none =>
              obtain ⟨item, evaluated, _⟩ := sound fallback (by simp [patternDefaults])
              rw [default_absent _ _ _ _ _ _ _ found, Logged.bind_result, evaluated]
              exact andThen_no_error _ _ (ihp item sound.tail.left) (ihr (.record fields) sound.tail.right)
          | some item =>
              rw [default_present _ _ _ _ _ _ _ _ found]
              exact andThen_no_error _ _ (ihp item sound.tail.left) (ihr (.record fields) sound.tail.right)
      | _ => exact ⟨_, rfl⟩
  | nil =>
      cases value with
      | list values => cases values <;> exact ⟨_, rfl⟩
      | _ => exact ⟨_, rfl⟩
  | cons p rest ihp ihr =>
      cases value with
      | list values =>
          cases values with
          | nil => exact ⟨_, rfl⟩
          | cons first tail => exact andThen_no_error _ _ (ihp first sound.left) (ihr (.list tail) sound.right)
      | _ => exact ⟨_, rfl⟩
  | snoc init last ihi ihl =>
      cases value with
      | list values =>
          simp only [CasePatterns.run]
          cases reversed : values.reverse with
          | nil => exact ⟨_, rfl⟩
          | cons item rest => exact andThen_no_error _ _ (ihi (.list rest.reverse) sound.left) (ihl item sound.right)
      | _ => exact ⟨_, rfl⟩
  | variant tag p ih =>
      cases value <;> simp only [CasePatterns.run]
      all_goals first | (split <;> first | exact ih _ sound | exact ⟨_, rfl⟩) | exact ⟨_, rfl⟩
  | nominal typeId ctorId p ih =>
      cases value <;> simp only [CasePatterns.run]
      all_goals first | (split <;> first | exact ih _ sound | exact ⟨_, rfl⟩) | exact ⟨_, rfl⟩
  | or p q ihp ihq =>
      obtain ⟨matched, ran⟩ := ihp value sound.left
      simp only [CasePatterns.run, Logged.bind_result, ran]
      cases matched with
      | none => exact ihq value sound.right
      | some bindings => exact ⟨_, rfl⟩
  | as p name ih =>
      obtain ⟨matched, ran⟩ := ih value sound
      simp only [CasePatterns.run, Logged.bind_result, ran]
      cases matched <;> exact ⟨_, rfl⟩


private theorem total_has_cell (total : Total defaults pattern input) (value : Value F)
    (valid : input.denote F value) :
    ∃ cell, Handles defaults pattern cell ∧ cell.denote F value := by
  obtain ⟨cell, partition, valid⟩ := domain_has_cell input value valid
  exact ⟨cell, (total_iff _ _ _).mp total cell partition, valid⟩

/-- A structurally total pattern really succeeds on every semantic value of
its domain. Float equality is unconstrained; only typed defaults must run. -/
theorem total_matches (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (defaults : D → Domain)
    (pattern : Pattern F D) (input : Domain) (total : Total defaults pattern input) (value : Value F)
    (valid : input.denote F value)
    (sound : DefaultsSoundFor defaults defaultEval (patternDefaults pattern)) :
    ∃ bindings, (CasePatterns.run floatCheck defaultEval pattern value).result = .ok (some bindings) := by
  induction pattern generalizing input value <;>
    obtain ⟨cell, handled, typed⟩ := total_has_cell total value valid
  case wildcard => exact ⟨[], rfl⟩
  case bind name => exact ⟨[(name, value)], rfl⟩
  case literal expected =>
    cases handled with
    | literal matched =>
        cases matched <;> change value = _ at typed <;> subst value <;>
          exact ⟨[], by simp [CasePatterns.run, matchCheck, success, Logged.ofResult]⟩
  case intRange lower upper =>
    cases handled with
    | intRange matched =>
        cases matched with
        | @int integer _ bounds =>
            change value = .literal (.int integer) at typed
            subst value
            have checked := (intRangeCheck_exact (FloatValue := F) lower upper (.int integer)).mpr (.int bounds)
            exact ⟨[], by simp [CasePatterns.run, checked, success, Logged.ofResult]⟩
  case pair p q ihp ihq =>
    cases handled with
    | pair first last =>
        cases value with
        | pair a b => exact andThen_matches _ _ (ihp _ first a typed.1 sound.left) (ihq _ last b typed.2 sound.right)
        | _ => cases typed
  case recordEnd =>
    cases handled with
    | recordEnd record =>
        obtain ⟨fields, same⟩ := record.values value typed
        subst value
        exact ⟨[], rfl⟩
  case field name p rest ihp ihr =>
    cases handled with
    | field selected head tail =>
        have itemTyped := selected.values value typed
        cases value with
        | record fields =>
            obtain ⟨item, found, itemValid⟩ := itemTyped
            simp only [CasePatterns.run, found]
            exact andThen_matches _ _ (ihp _ head item itemValid sound.left) (ihr _ tail (.record fields) typed sound.right)
        | _ => cases itemTyped
  case defaultField name fallback p rest ihp ihr =>
    cases handled with
    | defaultField selected head tail =>
        have optional := selected.values value typed
        cases value with
        | record fields =>
            cases found : lookup name fields with
            | some item =>
                rw [default_present _ _ _ _ _ _ _ _ found]
                exact andThen_matches _ _ (ihp _ head item (.inl (optional item found)) sound.tail.left)
                  (ihr _ tail (.record fields) typed sound.tail.right)
            | none =>
                obtain ⟨item, ran, itemValid⟩ := sound fallback (by simp [patternDefaults])
                rw [default_absent _ _ _ _ _ _ _ found, Logged.bind_result, ran]
                exact andThen_matches _ _ (ihp _ head item (.inr itemValid) sound.tail.left)
                  (ihr _ tail (.record fields) typed sound.tail.right)
        | _ => cases optional
  case nil =>
    cases handled
    change value = .list [] at typed
    subst value
    exact ⟨[], rfl⟩
  case cons p rest ihp ihr =>
    cases handled with
    | cons head tail =>
        cases value with
        | list values =>
            cases values with
            | nil => cases typed
            | cons first more =>
                exact andThen_matches _ _ (ihp _ head first typed.1 sound.left) (ihr _ tail (.list more) typed.2 sound.right)
        | _ => cases typed
  case snoc init last ihi ihl =>
    cases handled with
    | snoc first tail =>
        cases value with
        | list values =>
            cases values with
            | nil => cases typed
            | cons item more =>
                simp only [CasePatterns.run]
                cases reversed : (item :: more).reverse with
                | nil => simp at reversed
                | cons last rest =>
                    exact andThen_matches _ _
                      (ihi _ first (.list rest.reverse) (fun _ _ => trivial) sound.left)
                      (ihl _ tail last trivial sound.right)
        | _ => cases typed
  case variant tag p ih =>
    cases handled with
    | variant payload =>
        cases value with
        | variant name item =>
            obtain ⟨same, itemValid⟩ := typed
            subst name
            simpa [CasePatterns.run] using ih _ payload item itemValid sound
        | _ => cases typed
  case nominal typeId ctorId p ih =>
    cases handled with
    | nominal payload =>
        cases value with
        | nominal typeName ctorName item =>
            obtain ⟨sameType, sameCtor, itemValid⟩ := typed
            subst typeName; subst ctorName
            simpa [CasePatterns.run] using ih _ payload item itemValid sound
        | _ => cases typed
  case or p q ihp ihq =>
    cases handled with
    | orLeft first =>
        obtain ⟨bindings, ran⟩ := ihp _ first value typed sound.left
        exact ⟨bindings, by simp [CasePatterns.run, Logged.bind_result, ran, Except.bind, success, Logged.ofResult]⟩
    | orRight last =>
        obtain ⟨right, ranRight⟩ := ihq _ last value typed sound.right
        obtain ⟨matched, ranLeft⟩ := run_no_error floatCheck defaultEval defaults p value sound.left
        cases matched with
        | none => exact ⟨right, by simp [CasePatterns.run, Logged.bind_result, ranLeft, Except.bind, ranRight]⟩
        | some bindings => exact ⟨bindings, by simp [CasePatterns.run, Logged.bind_result, ranLeft, Except.bind,
            success, Logged.ofResult]⟩
  case as p name ih =>
    cases handled with
    | as inner =>
        obtain ⟨bindings, ran⟩ := ih _ inner value typed sound
        exact ⟨(name, value) :: bindings, by simp [CasePatterns.run, Logged.bind_result, ran,
          Except.bind, success, Logged.ofResult]⟩

/-- The main coverage-to-progress witness. The arm is in the original list,
has no guard, and matches the actual arbitrary input value. -/
theorem covered_matches (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (defaults : D → Domain)
    (arms : List (Arm F D))
    (input : Domain) (coverage : Covered defaults arms input) (value : Value F)
    (valid : input.denote F value)
    (sound : DefaultsSoundFor defaults defaultEval (armDefaults arms)) :
    ∃ arm ∈ arms, arm.guarded = false ∧
      ∃ bindings, (CasePatterns.run floatCheck defaultEval arm.pattern value).result = .ok (some bindings) := by
  obtain ⟨cell, partition, typed⟩ := domain_has_cell input value valid
  obtain ⟨arm, member, unguarded, total⟩ := (covered_iff _ _ _).mp coverage cell partition
  exact ⟨arm, member, unguarded, total_matches floatCheck defaultEval defaults _ _ total value typed (sound.arm member)⟩

theorem check_matches (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (defaults : D → Domain)
    (arms : List (Arm F D))
    (input : Domain) (checked : check defaults arms input = true) (value : Value F)
    (valid : input.denote F value)
    (sound : DefaultsSoundFor defaults defaultEval (armDefaults arms)) :
    ∃ arm ∈ arms, arm.guarded = false ∧
      ∃ bindings, (CasePatterns.run floatCheck defaultEval arm.pattern value).result = .ok (some bindings) :=
  covered_matches floatCheck defaultEval defaults arms input ((check_exact _ _ _).mp checked) value valid sound

/-- Semantic membership in a closed, tag-unique row of concrete domains. -/
def VariantHolds (row : VariantRow) : Ty F
  | .variant tag value => ∃ payload, Variants.Merged.lookup tag row = some payload ∧ payload.denote F value
  | _ => False

theorem variants_covered_matches (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (defaults : D → Domain)
    (arms : List (Arm F D))
    (row : VariantRow) (coverage : VariantsCovered defaults arms row) (value : Value F)
    (valid : VariantHolds row value)
    (sound : DefaultsSoundFor defaults defaultEval (armDefaults arms)) :
    ∃ arm ∈ arms, arm.guarded = false ∧
      ∃ bindings, (CasePatterns.run floatCheck defaultEval arm.pattern value).result = .ok (some bindings) := by
  cases value with
  | variant tag item =>
      obtain ⟨payload, found, typed⟩ := valid
      have total := (variantsCovered_iff _ _ _).mp coverage tag payload
        ((Variants.Merged.mem_iff_lookup tag payload row).mpr found)
      exact covered_matches floatCheck defaultEval defaults arms (.variant tag payload) total
        (.variant tag item) ⟨rfl, typed⟩ sound
  | _ => cases valid


/-- Erase code from arms for coverage, retaining pattern and guard presence. -/
def coverageArms (arms : List (CaseEvaluation.Arm F D G B)) : List (Arm F D) :=
  arms.map fun arm => ⟨arm.pattern, arm.guard.isSome⟩

private theorem actual_matching_arm (arms : List (CaseEvaluation.Arm F D G B))
    (floatCheck : F → F → Bool) (defaultEval : D → Logged E R (Value F)) (value : Value F)
    (matched : ∃ arm ∈ coverageArms arms, arm.guarded = false ∧
      ∃ bindings, (CasePatterns.run floatCheck defaultEval arm.pattern value).result = .ok (some bindings)) :
    ∃ arm ∈ arms, arm.guard = none ∧
      ∃ bindings, (CasePatterns.run floatCheck defaultEval arm.pattern value).result = .ok (some bindings) := by
  obtain ⟨projected, member, unguarded, result⟩ := matched
  change projected ∈ arms.map (fun arm => (⟨arm.pattern, arm.guard.isSome⟩ : Arm F D)) at member
  obtain ⟨actualArm, actualMember, same⟩ := List.mem_map.mp member
  subst projected
  exact ⟨actualArm, actualMember, by simpa using unguarded, result⟩

/-- A checked case cannot run out of matching arms. No successful-matching
premise is supplied: it is obtained from the checker and the input type. -/
theorem checked_arms_evaluate (floatCheck : F → F → Bool)
    (defaultEval : D → Logged (CaseEvaluation.Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (CaseEvaluation.Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (CaseEvaluation.Event E) R (Value F))
    (defaultTypes : D → Domain)
    (defaults : CasePatterns.DefaultSound DefaultTyped defaultEval)
    (guards : CaseEvaluation.GuardSound GuardTyped guardEval)
    (bodies : CaseEvaluation.BodySound BodyTyped bodyEval)
    (arms : List (CaseEvaluation.Arm F D G B)) (input : Domain)
    (defaultTyped : ∀ code ∈ armDefaults (coverageArms arms), DefaultTyped code ((defaultTypes code).denote F))
    (typed : ∀ arm ∈ arms, CaseEvaluation.ArmTyping DefaultTyped GuardTyped BodyTyped arm (input.denote F) target)
    (checked : check defaultTypes (coverageArms arms) input = true)
    (value : Value F) (valid : input.denote F value) (index : Nat) :
    ∃ result, (CaseEvaluation.runArms floatCheck defaultEval guardEval bodyEval value index arms).result =
      .ok (some result) ∧ target result := by
  have leafSound : DefaultsSoundFor defaultTypes defaultEval (armDefaults (coverageArms arms)) :=
    fun code used => defaults code _ (defaultTyped code used)
  have covered := actual_matching_arm arms floatCheck defaultEval value
    (check_matches floatCheck defaultEval defaultTypes (coverageArms arms) input checked value valid leafSound)
  exact CaseEvaluation.runArms_progress floatCheck defaultEval guardEval bodyEval
    defaults guards bodies arms typed value valid covered index

def ScrutineeSound (SourceTyped : S → Ty F → Prop)
    (sourceEval : S → Logged (CaseEvaluation.Event E) R (Value F)) : Prop :=
  ∀ source type, SourceTyped source type → ∃ value, (sourceEval source).result = .ok value ∧ type value

/-- Full case-node evaluation from independent leaf typing and an executable
coverage check, including successful typed evaluation of the scrutinee. -/
theorem checked_case_evaluates (floatCheck : F → F → Bool)
    (sourceEval : S → Logged (CaseEvaluation.Event E) R (Value F))
    (defaultEval : D → Logged (CaseEvaluation.Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (CaseEvaluation.Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (CaseEvaluation.Event E) R (Value F))
    (defaultTypes : D → Domain)
    (sources : ScrutineeSound SourceTyped sourceEval)
    (defaults : CasePatterns.DefaultSound DefaultTyped defaultEval)
    (guards : CaseEvaluation.GuardSound GuardTyped guardEval)
    (bodies : CaseEvaluation.BodySound BodyTyped bodyEval)
    (source : S) (arms : List (CaseEvaluation.Arm F D G B)) (input : Domain)
    (defaultTyped : ∀ code ∈ armDefaults (coverageArms arms), DefaultTyped code ((defaultTypes code).denote F))
    (sourceTyped : SourceTyped source (input.denote F))
    (typed : ∀ arm ∈ arms, CaseEvaluation.ArmTyping DefaultTyped GuardTyped BodyTyped arm (input.denote F) target)
    (checked : check defaultTypes (coverageArms arms) input = true) :
    ∃ result, (CaseEvaluation.eval floatCheck defaultEval guardEval bodyEval (sourceEval source) arms).result =
      .ok (some result) ∧ target result := by
  obtain ⟨value, ran, valid⟩ := sources source _ sourceTyped
  obtain ⟨result, selected, typedResult⟩ := checked_arms_evaluate floatCheck defaultEval guardEval bodyEval
    defaultTypes defaults guards bodies arms input defaultTyped typed checked value valid 0
  exact ⟨result, by simpa [CaseEvaluation.eval, Logged.bind_result, ran, Except.bind] using selected, typedResult⟩

/-- Reuse the nominally tag-unique row representation of the independent
pattern typing. Only payload descriptions are interpreted as semantic types. -/
def semanticRow (row : VariantRow) : Variants.Merged.Row Nat (Ty F) :=
  Variants.Merged.map (Domain.denote F) row

theorem variantHolds_semanticRow (row : VariantRow) (value : Value F) :
    VariantHolds row value ↔ Ty.variants (semanticRow row) value := by
  cases value with
  | variant tag item =>
      constructor
      · rintro ⟨payload, found, typed⟩
        refine ⟨payload.denote F, ?_, typed⟩
        apply (Variants.Merged.mem_iff_lookup tag _ _).mp
        exact List.mem_map.mpr ⟨(tag, payload), (Variants.Merged.mem_iff_lookup tag payload row).mpr found, rfl⟩
      · rintro ⟨payload, found, typed⟩
        have member := (Variants.Merged.mem_iff_lookup tag payload (semanticRow row)).mpr found
        obtain ⟨⟨key, domain⟩, member, same⟩ := List.mem_map.mp member
        obtain ⟨sameKey, samePayload⟩ := Prod.mk.inj same
        change key = tag at sameKey
        change domain.denote F = payload at samePayload
        subst key
        exact ⟨domain, (Variants.Merged.mem_iff_lookup tag domain row).mp member,
          by simpa only [samePayload] using typed⟩
  | _ => exact Iff.rfl

theorem checked_variant_arms_evaluate (floatCheck : F → F → Bool)
    (defaultEval : D → Logged (CaseEvaluation.Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (CaseEvaluation.Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (CaseEvaluation.Event E) R (Value F))
    (defaultTypes : D → Domain)
    (defaults : CasePatterns.DefaultSound DefaultTyped defaultEval)
    (guards : CaseEvaluation.GuardSound GuardTyped guardEval)
    (bodies : CaseEvaluation.BodySound BodyTyped bodyEval)
    (arms : List (CaseEvaluation.Arm F D G B)) (row : VariantRow)
    (defaultTyped : ∀ code ∈ armDefaults (coverageArms arms), DefaultTyped code ((defaultTypes code).denote F))
    (typed : ∀ arm ∈ arms, CaseEvaluation.ArmTyping DefaultTyped GuardTyped BodyTyped arm
      (Ty.variants (semanticRow row)) target)
    (checked : checkVariants defaultTypes (coverageArms arms) row = true)
    (value : Value F) (valid : Ty.variants (semanticRow row) value) (index : Nat) :
    ∃ result, (CaseEvaluation.runArms floatCheck defaultEval guardEval bodyEval value index arms).result =
      .ok (some result) ∧ target result := by
  have leafSound : DefaultsSoundFor defaultTypes defaultEval (armDefaults (coverageArms arms)) :=
    fun code used => defaults code _ (defaultTyped code used)
  have matched := variants_covered_matches floatCheck defaultEval defaultTypes
    (coverageArms arms) row ((checkVariants_exact _ _ _).mp checked) value
    ((variantHolds_semanticRow row value).mpr valid) leafSound
  exact CaseEvaluation.runArms_progress floatCheck defaultEval guardEval bodyEval defaults guards bodies
    arms typed value valid (actual_matching_arm arms floatCheck defaultEval value matched) index

theorem checked_variants_case_evaluates (floatCheck : F → F → Bool)
    (sourceEval : S → Logged (CaseEvaluation.Event E) R (Value F))
    (defaultEval : D → Logged (CaseEvaluation.Event E) R (Value F))
    (guardEval : G → Bindings F → Logged (CaseEvaluation.Event E) R Bool)
    (bodyEval : B → Bindings F → Logged (CaseEvaluation.Event E) R (Value F))
    (defaultTypes : D → Domain)
    (sources : ScrutineeSound SourceTyped sourceEval)
    (defaults : CasePatterns.DefaultSound DefaultTyped defaultEval)
    (guards : CaseEvaluation.GuardSound GuardTyped guardEval)
    (bodies : CaseEvaluation.BodySound BodyTyped bodyEval)
    (source : S) (arms : List (CaseEvaluation.Arm F D G B)) (row : VariantRow)
    (defaultTyped : ∀ code ∈ armDefaults (coverageArms arms), DefaultTyped code ((defaultTypes code).denote F))
    (sourceTyped : SourceTyped source (Ty.variants (semanticRow row)))
    (typed : ∀ arm ∈ arms, CaseEvaluation.ArmTyping DefaultTyped GuardTyped BodyTyped arm
      (Ty.variants (semanticRow row)) target)
    (checked : checkVariants defaultTypes (coverageArms arms) row = true) :
    ∃ result, (CaseEvaluation.eval floatCheck defaultEval guardEval bodyEval (sourceEval source) arms).result =
      .ok (some result) ∧ target result := by
  obtain ⟨value, ran, valid⟩ := sources source _ sourceTyped
  obtain ⟨result, selected, typedResult⟩ := checked_variant_arms_evaluate floatCheck defaultEval guardEval bodyEval
    defaultTypes defaults guards bodies arms row defaultTyped typed checked value valid 0
  exact ⟨result, by simpa [CaseEvaluation.eval, Logged.bind_result, ran, Except.bind] using selected, typedResult⟩

end Yulang.CaseCoverage
