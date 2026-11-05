import Yulang.DirectedBounds

/-!
# Pure cast execution and signed effect preservation

Spec §6.5 (2026-11-05) requires every declared cast body to be pure. A declaration
here contains its actual `Directed.Computation` body and a proved bound by its
inferred row. `Declaration.check` accepts exactly the empty signed row: a hidden
protected request or negative boundary debt is not mistaken for purity.

A typed conversion plan composes checked declarations, identity, products, sums,
and function wrappers. Input conversion at arrows runs contravariantly; output
conversion runs covariantly after the original call. There is deliberately no
constructor which maps inside an already constructed nominal container.

The main result preserves the actual request tree, including payloads, response
branches and signed weights, after erasing returned values. It implies an exact
correspondence of every effect-row bound. The arrow result compares an invocation
with the original function at the converted argument; pure conversion can change
values, so no equality with a call at an unconverted argument is asserted.

This is execution of resolved conversion plans in the existing well-founded
computation kernel. Obtaining the body bound from source typing and synthesizing
a plan from the ground `Casts` relation remain elaboration obligations. No source
termination theorem, equality of different cast paths, or recursive type model
is assumed or proved here.
-/

namespace Yulang.PureCasts

open Directed Directed.Computation

universe u
variable {n : Nat} {Key Payload Response A B C D : Type u}

/-- A value map executes only at a return; requests are forwarded unchanged. -/
def mapValue (f : A → B) : Computation n Key Payload Response A →
    Computation n Key Payload Response B
  | .pure value => .pure (f value)
  | .request occurrence payload resume =>
      .request occurrence payload (fun response => mapValue f (resume response))

theorem mapValue_comp (first : A → B) (second : B → C)
    (computation : Computation n Key Payload Response A) :
    mapValue second (mapValue first computation) = mapValue (second ∘ first) computation := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

theorem mapValue_allRequests (predicate : Occurrence n Key → Prop) (f : A → B)
    (computation : Computation n Key Payload Response A) :
    AllRequests predicate (mapValue f computation) ↔ AllRequests predicate computation := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      simp only [mapValue, AllRequests, ih]

theorem bind_pure_map (f : A → B) (computation : Computation n Key Payload Response A) :
    computation.bind (fun value => .pure (f value)) = mapValue f computation := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

/-- Empty-row boundedness rules out every request, not just capturable ones. -/
def pureValue (computation : Computation n Key Payload Response A)
    (bound : BoundedBy [] computation) : A := by
  cases computation with
  | pure value => exact value
  | request occurrence payload resume => exact False.elim (List.not_mem_nil bound.1)

theorem eq_pure_value (computation : Computation n Key Payload Response A)
    (bound : BoundedBy [] computation) : computation = .pure (pureValue computation bound) := by
  cases computation with
  | pure _ => rfl
  | request occurrence payload resume => exact False.elim (List.not_mem_nil bound.1)

structure Declaration (n : Nat) (Key Payload Response A B : Type u) where
  body : A → Computation n Key Payload Response B
  row : Row n Key
  bounded : ∀ argument, BoundedBy row (body argument)

def Declaration.check (declaration : Declaration n Key Payload Response A B) : Bool :=
  declaration.row.isEmpty

theorem Declaration.check_exact (declaration : Declaration n Key Payload Response A B) :
    declaration.check = true ↔ declaration.row = [] := by
  simp [Declaration.check]

theorem Declaration.checked_bound (declaration : Declaration n Key Payload Response A B)
    (accepted : declaration.check = true) (argument : A) :
    BoundedBy [] (declaration.body argument) := by
  rw [← declaration.check_exact.mp accepted]
  exact declaration.bounded argument

def Declaration.value (declaration : Declaration n Key Payload Response A B)
    (accepted : declaration.check = true) (argument : A) : B :=
  pureValue (declaration.body argument) (declaration.checked_bound accepted argument)

theorem Declaration.body_eq_pure (declaration : Declaration n Key Payload Response A B)
    (accepted : declaration.check = true) (argument : A) :
    declaration.body argument = .pure (declaration.value accepted argument) :=
  eq_pure_value _ _

theorem Declaration.rejects_nonempty (declaration : Declaration n Key Payload Response A B)
    (nonempty : declaration.row ≠ []) : declaration.check = false := by
  cases checked : declaration.check with
  | false => rfl
  | true => exact False.elim (nonempty (declaration.check_exact.mp checked))

/-- Resolved, typed conversion code. Nominal conversion appears only as an
explicit checked declaration for the entire source and target carriers. -/
inductive Plan (n : Nat) (Key Payload Response : Type u) : Type u → Type u → Type (u + 1) where
  | keep {A : Type u} : Plan n Key Payload Response A A
  | declared {A B : Type u} (declaration : Declaration n Key Payload Response A B)
      (accepted : declaration.check = true) : Plan n Key Payload Response A B
  | chain {A B C : Type u} : Plan n Key Payload Response A B → Plan n Key Payload Response B C →
      Plan n Key Payload Response A C
  | product {A B C D : Type u} : Plan n Key Payload Response A B → Plan n Key Payload Response C D →
      Plan n Key Payload Response (A × C) (B × D)
  | sum {A B C D : Type u} : Plan n Key Payload Response A B → Plan n Key Payload Response C D →
      Plan n Key Payload Response (Sum A C) (Sum B D)
  | arrow {A B C D : Type u} : Plan n Key Payload Response B A → Plan n Key Payload Response C D →
      Plan n Key Payload Response (A → Computation n Key Payload Response C)
        (B → Computation n Key Payload Response D)

/-- Execute every component conversion; at arrows construct the wrapper now,
while its argument and result conversions run at each later invocation. -/
def Plan.run : {A B : Type u} → Plan n Key Payload Response A B → A → Computation n Key Payload Response B
  | _, _, .keep, value => .pure value
  | _, _, .declared declaration _, value => declaration.body value
  | _, _, .chain first second, value => (first.run value).bind second.run
  | _, _, .product left right, value =>
      (left.run value.1).bind (fun first =>
        (right.run value.2).bind (fun second => .pure (first, second)))
  | _, _, .sum left _, .inl value => (left.run value).bind (fun result => .pure (.inl result))
  | _, _, .sum _ right, .inr value => (right.run value).bind (fun result => .pure (.inr result))
  | _, _, .arrow argument result, function => .pure (fun input =>
      (argument.run input).bind (fun converted => (function converted).bind result.run))

/-- The value-level meaning of a checked conversion. The arrow case keeps the
original request tree and transforms only the returned value. -/
def Plan.value : {A B : Type u} → Plan n Key Payload Response A B → A → B
  | _, _, .keep, value => value
  | _, _, .declared declaration accepted, value => declaration.value accepted value
  | _, _, .chain first second, value => second.value (first.value value)
  | _, _, .product left right, value => (left.value value.1, right.value value.2)
  | _, _, .sum left _, .inl value => .inl (left.value value)
  | _, _, .sum _ right, .inr value => .inr (right.value value)
  | _, _, .arrow argument result, function => fun input =>
      mapValue result.value (function (argument.value input))

/-- Purity is derived for all finite structural plans from checked base bodies. -/
theorem Plan.run_eq_pure (plan : Plan n Key Payload Response A B) (value : A) :
    plan.run value = .pure (plan.value value) := by
  induction plan with
  | keep => rfl
  | declared declaration accepted => exact declaration.body_eq_pure accepted value
  | chain first second ihFirst ihSecond =>
      simp only [run, Plan.value, ihFirst, Computation.bind]
      exact ihSecond _
  | product left right ihLeft ihRight =>
      simp only [run, Plan.value, ihLeft, ihRight, Computation.bind]
  | sum left right ihLeft ihRight =>
      cases value <;> simp only [run, Plan.value, ihLeft, ihRight, Computation.bind]
  | arrow argument result ihArgument ihResult =>
      apply congrArg Computation.pure
      funext input
      simp only [Plan.value, ihArgument, Computation.bind]
      have allResults : result.run = fun returned => .pure (result.value returned) :=
        funext ihResult
      rw [allResults, bind_pure_map]

/-- Boundary insertion sequences the conversion after the original expression. -/
def insert (plan : Plan n Key Payload Response A B)
    (computation : Computation n Key Payload Response A) :
    Computation n Key Payload Response B := computation.bind plan.run

theorem insert_eq_map (plan : Plan n Key Payload Response A B)
    (computation : Computation n Key Payload Response A) :
    insert plan computation = mapValue plan.value computation := by
  unfold insert
  have runPure : plan.run = fun returned => .pure (plan.value returned) :=
    funext plan.run_eq_pure
  rw [runPure, bind_pure_map]

/-- Erasing results retains the entire effect tree, not merely a chosen bound. -/
def requestTree (computation : Computation n Key Payload Response A) :
    Computation n Key Payload Response PUnit.{u + 1} := mapValue (fun _ => PUnit.unit) computation

theorem insert_requestTree (plan : Plan n Key Payload Response A B)
    (computation : Computation n Key Payload Response A) :
    requestTree (insert plan computation) = requestTree computation := by
  rw [insert_eq_map]
  exact mapValue_comp _ _ _

theorem insert_allRequests_iff (plan : Plan n Key Payload Response A B)
    (computation : Computation n Key Payload Response A) (predicate : Occurrence n Key → Prop) :
    AllRequests predicate (insert plan computation) ↔ AllRequests predicate computation := by
  rw [insert_eq_map]
  exact mapValue_allRequests _ _ _

theorem insert_bounded_iff (plan : Plan n Key Payload Response A B)
    (computation : Computation n Key Payload Response A) (row : Row n Key) :
    BoundedBy row (insert plan computation) ↔ BoundedBy row computation :=
  insert_allRequests_iff plan computation (fun occurrence => occurrence ∈ row)

def wrap (argument : Plan n Key Payload Response B A)
    (result : Plan n Key Payload Response C D)
    (function : A → Computation n Key Payload Response C) :
    B → Computation n Key Payload Response D := fun input =>
  (argument.run input).bind (fun converted => (function converted).bind result.run)

theorem arrow_constructs_without_effects (argument : Plan n Key Payload Response B A)
    (result : Plan n Key Payload Response C D)
    (function : A → Computation n Key Payload Response C) :
    (Plan.arrow argument result).run function = .pure (wrap argument result function) := rfl

theorem wrap_eq_insert (argument : Plan n Key Payload Response B A)
    (result : Plan n Key Payload Response C D)
    (function : A → Computation n Key Payload Response C) (input : B) :
    wrap argument result function input = insert result (function (argument.value input)) := by
  simp only [wrap, argument.run_eq_pure, Computation.bind, insert]

theorem wrapper_requestTree (argument : Plan n Key Payload Response B A)
    (result : Plan n Key Payload Response C D)
    (function : A → Computation n Key Payload Response C) (input : B) :
    requestTree (wrap argument result function input) =
      requestTree (function (argument.value input)) := by
  rw [wrap_eq_insert]
  exact insert_requestTree _ _

theorem wrapper_bounded_iff (argument : Plan n Key Payload Response B A)
    (result : Plan n Key Payload Response C D)
    (function : A → Computation n Key Payload Response C) (input : B) (row : Row n Key) :
    BoundedBy row (wrap argument result function input) ↔
      BoundedBy row (function (argument.value input)) := by
  rw [wrap_eq_insert]
  exact insert_bounded_iff _ _ _

/-- A declared latent row remains a valid latent row for every wrapped call. -/
theorem wrapper_preserves_latent_row (argument : Plan n Key Payload Response B A)
    (result : Plan n Key Payload Response C D)
    (function : A → Computation n Key Payload Response C) (row : Row n Key)
    (bounded : ∀ input, BoundedBy row (function input)) :
    ∀ input, BoundedBy row (wrap argument result function input) := by
  intro input
  exact (wrapper_bounded_iff argument result function input row).mpr (bounded _)

namespace Examples

private abbrev Tree (A : Type) := Computation 1 Nat Unit Unit A

def increment : Declaration 1 Nat Unit Unit Nat Nat where
  body := fun value => .pure (value + 1)
  row := []
  bounded := fun _ => trivial

def incrementPlan : Plan 1 Nat Unit Unit Nat Nat := .declared increment rfl

def noisy (occurrence : Occurrence 1 Nat) : Declaration 1 Nat Unit Unit Nat Nat where
  body := fun value => .request occurrence () (fun _ => .pure value)
  row := [occurrence]
  bounded := fun _ => ⟨by simp, fun _ => trivial⟩

theorem effectful_body_rejected : (noisy (raw 0)).check = false := rfl

theorem protected_body_rejected :
    (noisy (protect 0 allowNone (raw 0))).check = false := rfl

theorem negative_debt_body_rejected :
    (noisy (release 0 allowNone (raw 0))).check = false := rfl

def sourceFunction (value : Nat) : Tree Nat :=
  .request (release 0 allowNone (raw 0)) () (fun _ => .pure (value * 2))

theorem wrapper_keeps_negative_debt (input : Nat) :
    wrap incrementPlan incrementPlan sourceFunction input =
      (.request (release 0 allowNone (raw 0)) ()
        (fun _ => .pure ((input + 1) * 2 + 1)) : Tree Nat) := rfl

theorem wrapper_cannot_erase_nonempty_row (input : Nat) :
    ¬ BoundedBy [] (wrap incrementPlan incrementPlan sourceFunction input) := by
  intro bound
  exact List.not_mem_nil bound.1

end Examples
end Yulang.PureCasts
