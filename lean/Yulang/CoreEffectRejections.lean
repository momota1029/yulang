import Yulang.CoreEffectExamples

namespace Yulang.Core.EffectTyping.Examples
open Inference (Comp)

def deniedContract : Contract signature M :=
  { contract with permission := fun _ _ => false }

/-- Any result computation, regardless of reachability or action row. -/
theorem forbidden_multi_rejected (c : Comp M) :
    ¬ Typing M view deniedContract [] twoOperations c := by
  intro h
  cases h with
  | multiHandler allowed _ _ _ _ _ =>
    have impossible := allowed (0 : Fin 2)
    cases impossible

theorem forbidden_multi_no_solution (c : Comp M) :
    ¬ generate view deniedContract [] twoOperations c :=
  fun h => forbidden_multi_rejected c ((principal_exact _ _).mp h)

/-- Even a payload arm whose test always fails must pass the permission gate. -/
theorem forbidden_partial_rejected (c : Comp M) :
    ¬ Typing M view deniedContract [] partialTerm c := by
  intro h
  cases h with
  | partialHandler allowed _ _ _ _ _ =>
    have impossible := allowed (0 : Fin 1)
    cases impossible

def polymorphicSignature : LocalSignature M :=
  ⟨1, fun ι => ι 0, fun ι => ι 0⟩

def polymorphicContract : Contract signature M where
  operation := fun key => { toLocalSignature := polymorphicSignature, key := key }
  keySignature := fun _ => polymorphicSignature
  coherent := fun _ => rfl
  permission := fun _ _ => true

/-- The caller may instantiate the operation-local type with int. -/
theorem local_request_generated :
    generate view polymorphicContract [] (.request 0 (.lit .int))
      (.base .int, [Directed.raw 0]) := by
  apply (principal_exact _ _).mpr
  apply Typing.request (m := M) (contract := polymorphicContract) (op := 0) (ι := fun _ => .base .int)
  · exact .lit ⟨.refl _, SignedStructural.row_refl _⟩
  · exact .refl _
  · exact SignedStructural.row_refl _

private theorem payload_lower {Γ : List (Binding M signature)} {a : M.Ty} {c : Comp M}
    (h : Typing M view polymorphicContract (.mono (Comp.pure M a) :: Γ) (.var 0) c) :
    SignedStructural.Subtype a c.1 := by
  cases h with
  | var found bound =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    cases bound with
    | mono bound => exact bound.1

def escapingArm : Term := .handler 0 (.lit .int) (.lit .int) (.var 0)

/-- A concrete fixed int result cannot expose an arbitrary local payload type.
This is not rejection at every result upper bound (top would be different). -/
theorem local_escape_rejected :
    ¬ Typing M view polymorphicContract [] escapingArm (.base .int, []) := by
  intro h
  cases h with
  | handler _ _ _ operated upper _ =>
    have lower := payload_lower (operated (fun _ => .base .str))
    have bound := upper (fun _ => .base .str)
    exact StructuralBase.str_not_int
      (.trans lower (.trans (.unionRight _ _) bound))

theorem local_escape_no_solution :
    ¬ generate view polymorphicContract [] escapingArm (.base .int, []) :=
  fun h => local_escape_rejected ((principal_exact _ _).mp h)

end Yulang.Core.EffectTyping.Examples
