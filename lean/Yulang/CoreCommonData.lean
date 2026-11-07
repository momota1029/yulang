import Yulang.CorePresenceGeneration
import Yulang.CaseValues

/-!
# Structural data values in the common constructor judgment

This independent value judgment covers literals, pairs, finite record fields,
and variants. A record's first field is the outer insertion, so repeated labels
retain the existing first-wins interpretation. Every stored field is checked.
The rules retain the ordinary component rows and constructor subsumption; they
mention neither source typing nor formulas nor a solver.

The source lowering is proved exact for every presence model and every lexical
environment. Concrete data contain no variable occurrences, so the environment
does not affect their typing. Nominal identities and lists are explicitly
outside this stage; they are not encoded as structural variants.
-/

namespace Yulang.Core.CommonData

open PresenceGeneration (Model Comp)

abbrev Value := CaseValues.Value Empty

def literalBase : LiteralValues.Literal Empty → Inference.Base
  | .int _ => .int
  | .str _ => .str
  | .bool _ => .bool
  | .unit => .unit

@[simp] theorem literalBase_exact (value : LiteralValues.Literal Empty) :
    value.legacyBase = some (literalBase value) := by
  cases value <;> first | rfl | contradiction

def covered : Value → Bool
  | .literal _ => true
  | .pair first last => covered first && covered last
  | .record [] => true
  | .record ((_, head) :: rest) => covered head && covered (.record rest)
  | .variant _ payload => covered payload
  | .nominal _ _ _ | .list _ => false
termination_by value => sizeOf value

theorem covered_record_cons (field : Nat × Value) (rest : List (Nat × Value)) :
    covered (.record (field :: rest)) = (covered field.2 && covered (.record rest)) := by
  rcases field with ⟨name, value⟩
  simp only [covered]

def valueLower : Value → Inference.Expr
  | .literal value => .lit (literalBase value)
  | .pair first last => .pair (valueLower first) (valueLower last)
  | .record [] => .emptyRecord
  | .record ((name, head) :: rest) => .record name (valueLower head) (valueLower (.record rest))
  | .variant tag payload => .variant tag (valueLower payload)
  | .nominal _ _ _ | .list _ => .lit .unit
termination_by value => sizeOf value

theorem valueLower_record_cons (field : Nat × Value) (rest : List (Nat × Value)) :
    valueLower (.record (field :: rest)) =
      .record field.1 (valueLower field.2) (valueLower (.record rest)) := by
  rcases field with ⟨name, value⟩
  simp only [valueLower]

/-- Constructor rules for concrete structural values, independently of the
expression judgment and its implementation by constraint generation. -/
inductive ValueTyping (m : Model) : Value → Comp m → Prop where
  | literal : Comp.le m (Comp.pure m (m.base (literalBase value))) result →
      ValueTyping m (.literal value) result
  | pair : ValueTyping m first a → ValueTyping m last b →
      Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) result →
      ValueTyping m (.pair first last) result
  | emptyRecord : Comp.le m (Comp.pure m m.exactEmpty) result →
      ValueTyping m (.record []) result
  | record : ValueTyping m head a → ValueTyping m (.record rest) b →
      m.subTy b.1 m.emptyRecord →
      Comp.le m (m.record name a.1 b.1, m.join a.2 b.2) result →
      ValueTyping m (.record ((name, head) :: rest)) result
  | variant : ValueTyping m payload a →
      Comp.le m (m.variant tag a.1, a.2) result →
      ValueTyping m (.variant tag payload) result

theorem typing_covered {m : Model} {value : Value} {result : Comp m}
    (typed : ValueTyping m value result) : covered value = true := by
  induction typed <;> simp_all [covered]

private theorem record_head_smaller (field : Nat × Value) (rest : List (Nat × Value)) :
    sizeOf field.2 < sizeOf (.record (field :: rest) : Value) := by
  cases field
  simp
  omega

theorem valueLower_isValue (value : Value) (within : covered value = true) :
    (valueLower value).isValue = true := by
  cases value with
  | literal value => simp only [valueLower, Inference.Expr.isValue]
  | pair first last =>
      have parts : covered first = true ∧ covered last = true := by
        simpa only [covered, Bool.and_eq_true] using within
      simp only [valueLower, Inference.Expr.isValue, valueLower_isValue first parts.1,
        valueLower_isValue last parts.2, Bool.and_self]
  | record fields =>
      cases fields with
      | nil => simp only [valueLower, Inference.Expr.isValue]
      | cons field rest =>
          have smaller := record_head_smaller field rest
          have parts : covered field.2 = true ∧ covered (.record rest) = true := by
            simpa only [covered_record_cons, Bool.and_eq_true] using within
          simp only [valueLower_record_cons, Inference.Expr.isValue, valueLower_isValue field.2 parts.1,
            valueLower_isValue (.record rest) parts.2, Bool.and_self]
  | variant tag payload =>
      simpa only [valueLower, Inference.Expr.isValue] using
        valueLower_isValue payload (by simpa only [covered] using within)
  | nominal | list => simp [covered] at within
termination_by sizeOf value

theorem typing_lowered {m : Model} {value : Value} {result : Comp m}
    (typed : ValueTyping m value result) (environment : List (PresenceGeneration.Binding m)) :
    PresenceGeneration.Typing m environment (valueLower value) result := by
  induction typed with
  | literal bounded =>
      simp only [valueLower]
      exact .lit bounded
  | pair _ _ bounded first last =>
      simp only [valueLower]
      exact .pair first last bounded
  | emptyRecord bounded =>
      simp only [valueLower]
      exact .emptyRecord bounded
  | record _ _ recordType bounded head rest =>
      simp only [valueLower]
      exact .record head rest recordType bounded
  | variant _ bounded payload =>
      simp only [valueLower]
      exact .variant payload bounded

theorem typing_reflected {m : Model} (value : Value) (within : covered value = true)
    {environment : List (PresenceGeneration.Binding m)} {result : Comp m}
    (typed : PresenceGeneration.Typing m environment (valueLower value) result) :
    ValueTyping m value result := by
  cases value with
  | literal value =>
      simp only [valueLower] at typed
      cases typed with
      | lit bounded => exact .literal bounded
  | pair first last =>
      have parts : covered first = true ∧ covered last = true := by
        simpa only [covered, Bool.and_eq_true] using within
      simp only [valueLower] at typed
      cases typed with
      | pair before after bounded =>
          exact .pair (typing_reflected first parts.1 before)
            (typing_reflected last parts.2 after) bounded
  | record fields =>
      cases fields with
      | nil =>
          simp only [valueLower] at typed
          cases typed with
          | emptyRecord bounded => exact .emptyRecord bounded
      | cons field rest =>
          have smaller := record_head_smaller field rest
          have parts : covered field.2 = true ∧ covered (.record rest) = true := by
            simpa only [covered_record_cons, Bool.and_eq_true] using within
          simp only [valueLower_record_cons] at typed
          cases typed with
          | record head tail recordType bounded =>
              exact .record (typing_reflected field.2 parts.1 head)
                (typing_reflected (.record rest) parts.2 tail) recordType bounded
  | variant tag payload =>
      simp only [valueLower] at typed
      cases typed with
      | variant body bounded =>
          exact .variant
            (typing_reflected payload (by simpa only [covered] using within) body) bounded
  | nominal | list => simp [covered] at within
termination_by sizeOf value

/-- Every model, every covered concrete value, every lexical environment and
every result. No regularity, solver success or residual premise is used. -/
theorem typing_lower_exact (m : Model) (value : Value) (within : covered value = true)
    (environment : List (PresenceGeneration.Binding m)) (result : Comp m) :
    ValueTyping m value result ↔ PresenceGeneration.Typing m environment (valueLower value) result :=
  ⟨fun typed => typing_lowered typed environment, typing_reflected value within⟩

/-- The complete boundary also records the syntactic coverage of each value;
the fallback for nominal or list data can never certify a value typing. -/
theorem typing_lower_iff (m : Model) (value : Value)
    (environment : List (PresenceGeneration.Binding m)) (result : Comp m) :
    ValueTyping m value result ↔
      covered value = true ∧ PresenceGeneration.Typing m environment (valueLower value) result :=
  ⟨fun typed => ⟨typing_covered typed, typing_lowered typed environment⟩,
    fun ⟨within, typed⟩ => typing_reflected value within typed⟩

theorem lower_context_independent (m : Model) (value : Value) (within : covered value = true)
    (first last : List (PresenceGeneration.Binding m)) (result : Comp m) :
    PresenceGeneration.Typing m first (valueLower value) result ↔
      PresenceGeneration.Typing m last (valueLower value) result :=
  (typing_lower_exact m value within first result).symm.trans
    (typing_lower_exact m value within last result)

end Yulang.Core.CommonData
