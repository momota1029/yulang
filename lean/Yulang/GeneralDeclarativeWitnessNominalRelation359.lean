import Yulang.GeneralDeclarativeWitnessNominalSource359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNominalRelation359
open GeneralDeclarativeWitnessNominalSource359 (SlotRead Route lower argumentSlot Compared AtSource)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open CommonDeclaredNominalInspection (Registry Parameter)
open CommonRecursiveNominalIntervals (Endpoint Argument childContext effectiveParameter)
open GeneralDeclarativeWhere319 (Capture)

structure SourceUse (e : Environment) (table : Registry) (key arity : Nat)
    (params : List Parameter) : Prop where
  native : ∃ proof : Use e key arity,names proof.mode arity = some params
  current : table[key]? = some params

/-- This is a declarative derivation of the exact emitted operands. It has
no comparator call, captures chosen by a solver, or self-claimed evidence. -/
inductive Reads (e : Environment) (table : Registry) (slots : SlotRead) :
    Bool → Route → Endpoint Nat → Prop where
  | point {inherited binder c} : slots binder = some c →
      Reads e table slots inherited (.bind binder) (.ordinary (.var c.center))
  | const {inherited key} : SourceUse e table key 0 [] →
      Reads e table slots inherited (.nullary key) (.nominal key [])
  | atValue {inherited key binder c p} :
      SourceUse e table key 1 [p] → p.kind = .value →
      slots binder = some c → (effectiveParameter inherited p).variance ≠ .invariant →
      Reads e table slots inherited (.unary key (.bind binder))
        (.nominal key [.inl (.point (.ordinary (.var c.center)))])
  | atInterval {inherited key binder c p} :
      SourceUse e table key 1 [p] → p.kind = .value →
      slots binder = some c → (effectiveParameter inherited p).variance = .invariant →
      Reads e table slots inherited (.unary key (.bind binder))
        (.nominal key [.inl (.interval (.ordinary (.var c.lower)) (.ordinary (.var c.upper)))])
  | nested {inherited key other item p} :
      SourceUse e table key 1 [p] → p.kind = .value →
      (∀ k,other ≠ .bind k) →
      Reads e table slots (childContext inherited p) other item →
      Reads e table slots inherited (.unary key other) (.nominal key [.inl (.point item)])

theorem lower_sound {e table slots inherited route endpoint}
    (computed : lower e table slots inherited route = some endpoint) :
    Reads e table slots inherited route endpoint := by
  induction route generalizing inherited endpoint with
  | bind c =>
    cases bind : slots c with
    | none => simp [lower,bind] at computed
    | some item =>
      have fixed : .ordinary (.var item.center) = endpoint := by simpa [lower,bind] using computed
      rw [← fixed]
      exact .point bind
  | nullary key =>
    cases ctor : readUse e key 0 with
    | none => simp [lower,ctor] at computed
    | some use =>
      by_cases declared : names use.mode 0 = some [] ∧ table[key]? = some []
      · have fixed : .nominal key [] = endpoint := by simpa [lower,ctor,declared] using computed
        rw [← fixed]
        exact .const ⟨⟨use,declared.1⟩,declared.2⟩
      · simp [lower,ctor,declared] at computed
  | unary key arg ih =>
    cases ctor : readUse e key 1 with
    | none => simp [lower,ctor] at computed
    | some use =>
      cases modes : names use.mode 1 with
      | none => simp [lower,ctor,modes] at computed
      | some params =>
        cases params with
        | nil => simp [lower,ctor,modes] at computed
        | cons p rest =>
          cases rest with
          | cons q qs => simp [lower,ctor,modes] at computed
          | nil =>
            by_cases accepted : p.kind = .value ∧ table[key]? = some [p]
            · have source : SourceUse e table key 1 [p] := ⟨⟨use,modes⟩,accepted.2⟩
              cases arg with
              | bind binder =>
                cases value : slots binder with
                | none => simp [lower,ctor,modes,accepted,value] at computed
                | some item =>
                  have fixed : .nominal key [argumentSlot inherited p item] = endpoint := by
                    simpa [lower,ctor,modes,accepted,value] using computed
                  rw [← fixed]
                  by_cases effective : (effectiveParameter inherited p).variance = .invariant
                  · rw [argumentSlot,ite_eq_left effective]
                    exact .atInterval source accepted.1 value effective
                  · rw [argumentSlot,ite_eq_right effective]
                    exact .atValue source accepted.1 value effective
              | nullary n =>
                cases child : lower e table slots (childContext inherited p) (.nullary n) with
                | none =>
                  rw [lower] at computed
                  simp [bind,Option.bind,pure,ctor,modes,accepted,child] at computed
                | some item =>
                  have fixed : .nominal key [.inl (.point item)] = endpoint := by
                    rw [lower] at computed
                    simpa [bind,Option.bind,pure,ctor,modes,accepted,child] using computed
                  rw [← fixed]
                  exact .nested source accepted.1 (by intro i h; cases h) (ih child)
              | unary n inner =>
                cases child : lower e table slots (childContext inherited p) (.unary n inner) with
                | none =>
                  rw [lower] at computed
                  simp [bind,Option.bind,pure,ctor,modes,accepted,child] at computed
                | some item =>
                  have fixed : .nominal key [.inl (.point item)] = endpoint := by
                    rw [lower] at computed
                    simpa [bind,Option.bind,pure,ctor,modes,accepted,child] using computed
                  rw [← fixed]
                  exact .nested source accepted.1 (by intro i h; cases h) (ih child)
            · cases arg <;> simp [lower,ctor,modes,accepted] at computed

theorem checked_operand_meaning {e table slots inherited left right a b}
    (w : Compared e table slots inherited left right a b) :
    AtSource e left a ∧ AtSource e right b ∧
      Reads e table slots inherited a w.first.endpoint ∧
      Reads e table slots inherited b w.last.endpoint :=
  ⟨w.first.source,w.last.source,lower_sound w.first.lowered,lower_sound w.last.lowered⟩

end Yulang.GeneralDeclarativeWitnessNominalRelation359
