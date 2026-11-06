import Yulang.CaseDataProgram

/-!
# Joint coverage of a merged polyvariant payload (answered Q8)

Different unguarded arms may cover different cells of the same payload.
The old conservative checker and its boundary theorems remain unchanged.
This extension reuses its structural payload partition and adds a checked
route to the actual case evaluator.  Residual rows always keep or remove a
whole tag; no partial payload type is manufactured.
-/

namespace Yulang.JointCaseCoverage

open CaseValues CasePatterns CaseCoverage LiteralValues EvaluationTrace

inductive TagCovered (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D))
    (tag : Nat) (payload : Domain) : Prop where
  | whole : Covered defaults arms (.variant tag payload) → TagCovered defaults arms tag payload
  | parts : (∀ cell, Cell payload cell → Covered defaults arms (.variant tag cell)) →
      TagCovered defaults arms tag payload

def checkTag (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D))
    (tag : Nat) (payload : Domain) : Bool :=
  check defaults arms (.variant tag payload) ||
    (cells payload).all (fun cell => check defaults arms (.variant tag cell))

theorem checkTag_exact (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D))
    (tag : Nat) (payload : Domain) :
    checkTag defaults arms tag payload = true ↔ TagCovered defaults arms tag payload := by
  simp only [checkTag, Bool.or_eq_true, List.all_eq_true, cells_exact, check_exact]
  constructor
  · exact fun covered => covered.elim TagCovered.whole TagCovered.parts
  · intro covered
    cases covered with
    | whole h => exact .inl h
    | parts h => exact .inr h

theorem old_check_preserved (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D))
    (tag : Nat) (payload : Domain) (checked : check defaults arms (.variant tag payload) = true) :
    checkTag defaults arms tag payload = true := by simp [checkTag, checked]

theorem guarded_cons_ignored (defaults : D → Domain) (arm : CaseCoverage.Arm F D)
    (arms : List (CaseCoverage.Arm F D)) (tag : Nat) (payload : Domain)
    (guarded : arm.guarded = true) :
    checkTag defaults (arm :: arms) tag payload = checkTag defaults arms tag payload := by
  simp only [checkTag, CaseCoverage.guarded_cons_ignored defaults arm arms _ guarded]

inductive RowCovered (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D))
    (row : VariantRow) : Prop where
  | tags : (∀ tag payload, (tag, payload) ∈ row.entries → TagCovered defaults arms tag payload) →
      RowCovered defaults arms row

def checkRow (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D)) (row : VariantRow) : Bool :=
  row.entries.all fun entry => checkTag defaults arms entry.1 entry.2

theorem rowCovered_iff (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D)) (row : VariantRow) :
    RowCovered defaults arms row ↔
      ∀ tag payload, (tag, payload) ∈ row.entries → TagCovered defaults arms tag payload := by
  constructor
  · intro covered; cases covered with | tags h => exact h
  · exact .tags

theorem checkRow_exact (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D)) (row : VariantRow) :
    checkRow defaults arms row = true ↔ RowCovered defaults arms row := by
  rw [rowCovered_iff]
  simp only [checkRow, List.all_eq_true, checkTag_exact]
  constructor
  · exact fun covered tag payload member => covered (tag, payload) member
  · exact fun covered ⟨tag, payload⟩ member => covered tag payload member

def handledTag (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D))
    (row : VariantRow) (tag : Nat) : Bool :=
  match Variants.Merged.lookup tag row with
  | none => false
  | some payload => checkTag defaults arms tag payload

def residual (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D)) (row : VariantRow) : VariantRow :=
  Variants.Merged.residual (handledTag defaults arms row) row

theorem residual_lookup (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D))
    (row : VariantRow) (tag : Nat) :
    Variants.Merged.lookup tag (residual defaults arms row) =
      match Variants.Merged.lookup tag row with
      | none => none
      | some payload => if checkTag defaults arms tag payload then none else some payload := by
  rw [residual, Variants.Merged.lookup_residual]
  cases found : Variants.Merged.lookup tag row <;> simp [handledTag, found]

theorem residual_empty_iff (defaults : D → Domain) (arms : List (CaseCoverage.Arm F D)) (row : VariantRow) :
    (residual defaults arms row).entries = [] ↔ RowCovered defaults arms row := by
  rw [residual, Variants.Merged.residual_empty_iff, rowCovered_iff]
  constructor
  · intro empty tag payload member
    have found := (Variants.Merged.mem_iff_lookup tag payload row).mp member
    exact (checkTag_exact _ _ _ _).mp (by simpa [handledTag, found] using empty tag payload found)
  · intro covered tag payload found
    have valid := covered tag payload ((Variants.Merged.mem_iff_lookup tag payload row).mpr found)
    simpa [handledTag, found] using (checkTag_exact _ _ _ _).mpr valid

theorem tag_covered_matches (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (defaults : D → Domain)
    (arms : List (CaseCoverage.Arm F D)) (tag : Nat) (payload : Domain)
    (covered : TagCovered defaults arms tag payload) (value : Value F)
    (valid : payload.denote F value)
    (sound : DefaultsSoundFor defaults defaultEval (armDefaults arms)) :
    ∃ arm ∈ arms, arm.guarded = false ∧
      ∃ bindings, (CasePatterns.run floatCheck defaultEval arm.pattern (.variant tag value)).result =
        .ok (some bindings) := by
  cases covered with
  | whole total =>
      exact covered_matches floatCheck defaultEval defaults arms _ total (.variant tag value) ⟨rfl, valid⟩ sound
  | parts total =>
      obtain ⟨cell, partition, holds⟩ := domain_has_cell payload value valid
      exact covered_matches floatCheck defaultEval defaults arms _ (total cell partition)
        (.variant tag value) ⟨rfl, holds⟩ sound

theorem row_covered_matches (floatCheck : F → F → Bool)
    (defaultEval : D → Logged E R (Value F)) (defaults : D → Domain)
    (arms : List (CaseCoverage.Arm F D)) (row : VariantRow)
    (covered : RowCovered defaults arms row) (value : Value F)
    (valid : VariantHolds row value)
    (sound : DefaultsSoundFor defaults defaultEval (armDefaults arms)) :
    ∃ arm ∈ arms, arm.guarded = false ∧
      ∃ bindings, (CasePatterns.run floatCheck defaultEval arm.pattern value).result = .ok (some bindings) := by
  cases value with
  | variant tag item =>
      obtain ⟨payload, found, holds⟩ := valid
      exact tag_covered_matches floatCheck defaultEval defaults arms tag payload
        ((rowCovered_iff _ _ _).mp covered tag payload ((Variants.Merged.mem_iff_lookup _ _ _).mpr found))
        item holds sound
  | _ => cases valid

/-- Soundness reaches the existing concrete data-case evaluator; only its
independent source/leaf typing and the checked joint coverage are premises. -/
theorem checked_program_evaluates (floatCheck : F → F → Bool)
    (types : List (Nat × Ty F)) (defaultDomains : CaseDataTerms.Expr F → Domain)
    (program : CaseDataProgram.Program F) (row : VariantRow)
    (scrutinee : CaseDataTerms.Typing types program.scrutinee (Ty.variants (semanticRow row)))
    (defaults : ∀ code ∈ armDefaults (coverageArms program.arms),
      CaseDataTerms.Typing types code ((defaultDomains code).denote F))
    (arms : ∀ arm ∈ program.arms,
      CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped types) (CaseDataTerms.GuardTyped types)
        (CaseDataTerms.BodyTyped types) arm (Ty.variants (semanticRow row)) target)
    (checked : checkRow defaultDomains (coverageArms program.arms) row = true)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    ∃ result, (CaseDataProgram.eval floatCheck outer program).result = .ok (some result) ∧ target result := by
  obtain ⟨value, evaluated, typed⟩ := CaseDataTerms.typing_evaluates scrutinee outer valid
  have defaultSound := CaseDataTerms.default_sound outer types valid
  have leafSound : DefaultsSoundFor defaultDomains (CaseDataTerms.defaultEval outer)
      (armDefaults (coverageArms program.arms)) := fun code used => defaultSound code _ (defaults code used)
  obtain ⟨projected, member, unguarded, matched⟩ := row_covered_matches floatCheck
    (CaseDataTerms.defaultEval outer) defaultDomains (coverageArms program.arms) row
    ((checkRow_exact _ _ _).mp checked) value ((variantHolds_semanticRow _ _).mpr typed) leafSound
  obtain ⟨actual, actualMember, same⟩ := List.mem_map.mp member
  subst projected
  have matching : ∃ arm ∈ program.arms, arm.guard = none ∧
      ∃ bindings, (CasePatterns.run floatCheck (CaseDataTerms.defaultEval outer) arm.pattern value).result =
        .ok (some bindings) := ⟨actual, actualMember, by simpa using unguarded, matched⟩
  obtain ⟨result, selected, resultTyped⟩ := CaseEvaluation.runArms_progress floatCheck
    (CaseDataTerms.defaultEval outer) (CaseDataTerms.guardEval outer) (CaseDataTerms.bodyEval outer)
    defaultSound (CaseDataTerms.guard_sound outer types valid) (CaseDataTerms.body_sound outer types valid)
    program.arms arms value typed matching 0
  exact ⟨result, by simpa [CaseDataProgram.eval, CaseEvaluation.eval, Logged.bind_result,
    evaluated, Except.bind] using selected, resultTyped⟩

namespace Examples

def booleanPayloadArms : List (CaseCoverage.Arm F Empty) :=
  [⟨.variant 0 (.literal (.bool false)), false⟩,
   ⟨.variant 0 (.literal (.bool true)), false⟩]

theorem boolean_payload_jointly_covered :
    checkTag (F := F) Empty.elim booleanPayloadArms 0 (.base .bool) = true := rfl

theorem boolean_payload_removed :
    (residual (F := F) Empty.elim booleanPayloadArms
      (Variants.Merged.normalize Domain.union [(0, .base .bool)])).entries = [] := rfl

theorem guarded_half_retains_payload :
    (residual (F := F) Empty.elim
      [⟨.variant 0 (.literal (.bool false)), false⟩,
       ⟨.variant 0 (.literal (.bool true)), true⟩]
      (Variants.Merged.normalize Domain.union [(0, .base .bool)])).entries = [(0, .base .bool)] := rfl

/-- Float literals do not count for exhaustiveness, including within a tag. -/
theorem float_literal_not_coverage (value : F) (tag : Nat) :
    checkTag (D := Empty) Empty.elim [⟨.variant tag (.literal (.float value)), false⟩]
      tag (.base .float) = false := by simp [checkTag, check, cells, checkOne, literalCellCheck]

end Examples
end Yulang.JointCaseCoverage
