import Yulang.CommonCaseRecordReadout
import Yulang.CommonPurePatternMatching

/-! A successful pure pattern on a minimal record cell transfers to its
original record with arbitrary extra fields. Acceptance is transferred, not
the representative's binding payloads: the real matcher retains the original
subject and original field values. -/

namespace Yulang.CommonCaseRecordMatching

open CaseValues (Value Bindings lookup)
open CasePatterns (Pattern)
open EvaluationTrace (Logged)
open CommonCaseBaseCells (Supported ValueEquivalent)
open CommonCaseRecordCells (Specification EntriesRelated)
open CommonPurePatternMatching (bindings)

def accepts (floatCheck : F → F → Bool) (pattern : Pattern F Empty) (value : Value F) : Bool :=
  (bindings floatCheck pattern value).isSome

theorem accepts_field (floatCheck : F → F → Bool) (name : Nat) (p rest : Pattern F Empty) (fields : Bindings F) :
    accepts floatCheck (.field name p rest) (.record fields) = match lookup name fields with
      | none => false
      | some value => accepts floatCheck p value && accepts floatCheck rest (.record fields) := by
  cases found : lookup name fields <;> simp only [accepts, bindings, found, Option.bind_none, Option.bind_some] <;> try rfl
  exact CommonPurePatternMatching.combine_isSome _ _

theorem accepts_or (floatCheck : F → F → Bool) (p q : Pattern F Empty) (value : Value F) :
    accepts floatCheck (.or p q) value = (accepts floatCheck p value || accepts floatCheck q value) := by
  simp only [accepts, bindings]
  cases bindings floatCheck p value <;> rfl

theorem accepts_as (floatCheck : F → F → Bool) (p : Pattern F Empty) (name : Nat) (value : Value F) :
    accepts floatCheck (.as p name) value = accepts floatCheck p value := Option.isSome_map

theorem supported_bindings (floatCheck : Empty → Empty → Bool) (pattern : Pattern Empty Empty)
    (value : Value Empty) (supported : Supported value) :
    bindings floatCheck pattern value = CommonCaseBaseMatching.structuralBindings pattern value := by
  have first := CommonPurePatternMatching.run_exact (E := Empty) (R := Empty) floatCheck
    (fun _ => Empty.elim) [] pattern value
  have last := CommonCaseBaseMatching.run_supported_exact (E := Empty) (R := Empty) floatCheck
    (fun _ => Empty.elim) pattern [] value supported
  exact Except.ok.inj (congrArg Logged.result (first.symm.trans last))

theorem equivalent_supported (same : ValueEquivalent bounds texts first last) : Supported first ∧ Supported last := by
  induction same with
  | literal => exact ⟨.literal, .literal⟩
  | pair left right ihl ihr => exact ⟨.pair ihl.1 ihr.1, .pair ihl.2 ihr.2⟩
  | variant child ih => exact ⟨.variant ih.1, .variant ih.2⟩

theorem supported_accepts_congr (floatCheck : Empty → Empty → Bool) (pattern : Pattern Empty Empty)
    (same : ValueEquivalent bounds texts first last)
    (boundsIncluded : ∀ bound ∈ CommonCaseBaseMatching.boundaries pattern, bound ∈ bounds)
    (textsIncluded : ∀ text ∈ CommonCaseBaseMatching.texts pattern, text ∈ texts) :
    accepts floatCheck pattern first = accepts floatCheck pattern last := by
  have support := equivalent_supported same
  simp only [accepts, supported_bindings floatCheck pattern first support.1,
    supported_bindings floatCheck pattern last support.2]
  exact CommonCaseBaseMatching.accepts_congr pattern same boundsIncluded textsIncluded

theorem related_names (related : EntriesRelated bounds texts actual specification samples) :
    samples.map Prod.fst = specification.map Prod.fst := by
  induction related <;> simp_all

theorem lookup_mem_names (fields : Bindings F) (name : Nat) (value : Value F) (found : lookup name fields = some value) :
    name ∈ fields.map Prod.fst := by
  apply (CommonPatternBindingAlignment.lookup_isSome name fields).mp
  rw [CommonPatternBindingAlignment.lookup_values, found]
  rfl

/-- All source pure patterns, every record domain and every actual record
order/duplicate/extra field. A minimal successful cell can only inspect fields
declared by its specification; actual extra fields cannot invalidate it. -/
theorem record_accepts_transfer (floatCheck : Empty → Empty → Bool) (pattern : Pattern Empty Empty)
    (related : EntriesRelated bounds texts actual specification samples)
    (boundsIncluded : ∀ bound ∈ CommonCaseBaseMatching.boundaries pattern, bound ∈ bounds)
    (textsIncluded : ∀ text ∈ CommonCaseBaseMatching.texts pattern, text ∈ texts)
    (accepted : accepts floatCheck pattern (.record samples) = true) :
    accepts floatCheck pattern (.record actual) = true := by
  induction pattern with
  | wildcard | bind | recordEnd => rfl
  | literal | intRange | pair | nil | cons | snoc | variant | nominal => cases accepted
  | defaultField name impossible => exact impossible.elim
  | field name p rest ihp ihr =>
      rw [accepts_field] at accepted ⊢
      cases found : lookup name samples with
      | none => simp only [found, Bool.false_eq_true] at accepted
      | some item =>
          have member := lookup_mem_names samples name item found
          rw [related_names related] at member
          obtain ⟨sample, original, sampleFound, originalFound, same⟩ := related.lookup_related name member
          have equal : sample = item := Option.some.inj (sampleFound.symm.trans found)
          subst sample
          simp only [found, Bool.and_eq_true] at accepted
          rw [originalFound, Bool.and_eq_true]
          constructor
          · rw [← supported_accepts_congr floatCheck p same
              (fun bound member => boundsIncluded bound (List.mem_append_left _ member))
              (fun text member => textsIncluded text (List.mem_append_left _ member))]
            exact accepted.1
          · exact ihr (fun bound member => boundsIncluded bound (List.mem_append_right _ member))
              (fun text member => textsIncluded text (List.mem_append_right _ member)) accepted.2
  | or p q ihp ihq =>
      rw [accepts_or, Bool.or_eq_true] at accepted ⊢
      rcases accepted with left | right
      · exact Or.inl (ihp (fun bound member => boundsIncluded bound (List.mem_append_left _ member))
          (fun text member => textsIncluded text (List.mem_append_left _ member)) left)
      · exact Or.inr (ihq (fun bound member => boundsIncluded bound (List.mem_append_right _ member))
          (fun text member => textsIncluded text (List.mem_append_right _ member)) right)
  | as p name ih =>
      rw [accepts_as] at accepted ⊢
      exact ih boundsIncluded textsIncluded accepted

theorem matches_exact (floatCheck : F → F → Bool) (defaultEval : Bindings F → Empty → Logged E R (Value F))
    (environment : Bindings F) (pattern : Pattern F Empty) (value : Value F) :
    (∃ returned, (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result = .ok (some returned)) ↔
      accepts floatCheck pattern value = true := by
  simp only [CommonPurePatternMatching.run_exact, Logged.ofResult, Except.ok.injEq, accepts]
  exact Option.isSome_iff_exists.symm

end Yulang.CommonCaseRecordMatching
