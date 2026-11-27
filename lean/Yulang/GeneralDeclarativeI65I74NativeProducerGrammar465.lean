import Yulang.GeneralDeclarativeWitnessNativeOrder362

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NativeProducer465
open CommonRecursiveNominalIntervals (Endpoint Bounds)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNativeOrder362 (node)

/-- Exact image of the existing NativeValue360 endpoint projection.
It is a statement about emitted syntax, not type equivalence. -/
inductive EmittedSyntax : Endpoint Nat → Prop where
  | variable : EmittedSyntax (.ordinary (.var n))
  | nullary : EmittedSyntax (.nominal key [])
  | unary : EmittedSyntax child → EmittedSyntax (.nominal key [.inl (.point child)])

theorem every_emitted_node_has_its_literal_compiler_grammar (c : Code) :
    EmittedSyntax (node c) := by
  induction c with
  | leaf => exact .variable
  | nullary => exact .nullary
  | unary _ _ ih => exact .unary ih

theorem literal_compiler_grammar_is_exactly_the_image (e : Endpoint Nat) :
    EmittedSyntax e ↔ ∃ c : Code, node c = e := by
  constructor
  · intro h
    induction h with
    | «variable» => exact ⟨.leaf _,rfl⟩
    | nullary => exact ⟨.nullary _,rfl⟩
    | unary _ ih =>
      obtain ⟨child,rfl⟩ := ih
      exact ⟨.unary _ child,rfl⟩
  · rintro ⟨c,rfl⟩
    exact every_emitted_node_has_its_literal_compiler_grammar c

theorem compiler_node_is_injective : Function.Injective node := by
  intro first
  induction first with
  | leaf n =>
    intro last h
    cases last <;> simp_all [node]
  | nullary k =>
    intro last h
    cases last <;> simp_all [node]
  | unary k c ih =>
    intro last h
    cases last with
    | leaf => simp [node] at h
    | nullary => simp [node] at h
    | unary l d =>
      have data : k = l ∧ node c = node d := by simpa [node] using h
      rw [data.1,ih data.2]

theorem concrete_nonvariable_ordinary_source_is_never_native360_emission
    (c : Code) (term : Yulang.Core.PresenceGeneration.TyTerm Nat)
    (proper : ∀ name, term ≠ .var name) :
    node c ≠ .ordinary term := by
  intro e
  have shape := e ▸ every_emitted_node_has_its_literal_compiler_grammar c
  cases shape
  exact proper _ rfl

theorem exact_ordinary_record_owner_is_not_an_emitted_native360_node
    (c : Code) (label : Nat) (payload tail : Yulang.Core.PresenceGeneration.TyTerm Nat) :
    node c ≠ .ordinary (.record label payload tail) := by
  apply concrete_nonvariable_ordinary_source_is_never_native360_emission
  intro n h
  cases h

end Yulang.GeneralDeclarativeI65.I72.NativeProducer465
