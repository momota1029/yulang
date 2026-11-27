import Yulang.GeneralDeclarativeI65B6MixedLexical401
import Yulang.GeneralDeclarativeI65I74ReadyHeadCaptureReceipt466

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466LexicalHeadProjection
open Yulang.GeneralDeclarativeI65
open Yulang.Core.PresenceGeneration (TyTerm)
open Yulang.CommonNominalFullCarrier (model)

mutual
/-- Syntax-only projection from an independently supplied typed lexical B6 input. Does not
bind a new physical slot, choose a release or open an unsupported join. -/
def project {s slots c p} : NamedMixedTree401 s slots c p → Option (TyTerm Nat)
  | .binder _ read => some (.var read.val.center)
  | .record label a b => do return .record label (← project a) (← project b)
  | .variant tag a => (project a).map (.variant tag)
  | .join .. => none
  | .declaredApp .. => none
  | .scalar _ b _ _ => some (.base b)
  | .emptyRecord .. => some .emptyRecord
  | .exactEmpty .. => some .exactEmpty
  | .pair _ _ _ a b => do return .pair (← project a) (← project b)
end

theorem projects_the_same_value_in_each_model {s slots c p}
    (tree : NamedMixedTree401 s slots c p) (m : Model) (t : TyTerm Nat)
    (ok : project tree = some t) :
    evaluateMixedRhs401 (actualNamedMixedRead401 m) tree = some (t.eval model m.assignment) := by
  fun_induction project tree generalizing t with
  | case1 =>
    cases Option.some.inj ok
    rfl
  | case2 ctx p₁ p₂ label a b ihA ihB =>
    cases pa : project a <;> simp [pa,Option.bind] at ok
    rename_i a'
    cases pb : project b <;> simp [pb] at ok
    cases ok
    simp [evaluateMixedRhs401,ihA _ pa,ihB _ pb,TyTerm.eval,model]
  | case3 ctx p₁ tag a ih =>
    cases pa : project a <;> simp [pa] at ok
    cases ok
    simp [evaluateMixedRhs401,ih _ pa,TyTerm.eval,model]
  | case4 => cases ok
  | case5 => cases ok
  | case6 =>
    cases Option.some.inj ok
    rfl
  | case7 =>
    cases Option.some.inj ok
    rfl
  | case8 =>
    cases Option.some.inj ok
    rfl
  | case9 ctx p₁ p₂ n use shape a b ihA ihB =>
    cases pa : project a <;> simp [pa,Option.bind] at ok
    rename_i a'
    cases pb : project b <;> simp [pb] at ok
    cases ok
    simp [evaluateMixedRhs401,ihA _ pa,ihB _ pb,TyTerm.eval,model]
    rfl


open Yulang.C466WrittenBinderCoordinates
open Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65.I72.Checker408 (Problem)
open Yulang.GeneralDeclarativeOrigins321 (Supported restriction)
open Yulang.GeneralDeclarativeNestedView332 (Sources)
open Yulang.GeneralDeclarativeWhere319 (Capture)
open Yulang.GeneralDeclarationPatterns (normalize Pattern)

/-- Use the same finite capture table actually emitted by old assembly,
not a postulated semantic assignment or authority. This uses the legacy
list lookup; it does not prove repeated captures are interchangeable. -/
def exactLegacyCaptureSlots {p : Problem} {table : CheckedTable p.state.core.current}
    (r : CheckedCaptureHead p table) (name : Nat) : Option Capture :=
  r.allocated.captures.lookup name

def readyReifiedHead {p : Problem} {table : CheckedTable p.state.core.current}
    (r : CheckedCaptureHead p table)
    (typedShape : B6MixedRhs401 p.state.core false (normalize r.original.orig.original)) :
    Option (TyTerm Nat) := do
  let written ← substituteMixedRhs401 (instantiateName401 (exactLegacyCaptureSlots r)) typedShape
  project written

theorem actual_emitted_capture_slots_project_the_same_original_typed_head_value
    {p : Problem} {table : CheckedTable p.state.core.current} (r : CheckedCaptureHead p table)
    (typedShape : B6MixedRhs401 p.state.core false (normalize r.original.orig.original)) (word : TyTerm Nat)
    (computed : readyReifiedHead r typedShape = some word) :
    ∀ m : Model, evaluateMixedRhs401 (sourceRead401 m (exactLegacyCaptureSlots r)) typedShape =
      some (word.eval model m.assignment) := by
  intro m
  cases res : substituteMixedRhs401 (instantiateName401 (exactLegacyCaptureSlots r)) typedShape with
  | none => simp [readyReifiedHead,res,Option.bind] at computed
  | some tree =>
    have hit : project tree = some word := by simpa [readyReifiedHead,res,Option.bind] using computed
    have ⟨out,first,last⟩ := source_and_lexically_instantiated_tree_read_same_model401 typedShape tree res m
    have exactValue := projects_the_same_value_in_each_model tree m word hit
    exact last.trans (first.symm.trans exactValue)

end Yulang.C466LexicalHeadProjection
