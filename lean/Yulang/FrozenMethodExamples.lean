import Yulang.FrozenMethods
import Yulang.QualifiedExamples

/-!
# A same-named field does not change a frozen role method

`f(x) = x.size` is selected at an unknown receiver and stores `Size` as a
qualifier. Definition checking works under the abstract dictionary, without
requiring an impl. A later call at a record-shaped `box` containing `size`
still requires `Size box`. The actual generated principal and stored qualified
scheme both reject that caller when no impl is visible.

In the contrasting SCC snapshot the receiver is already known to contain the
field: selection produces a field access, and the real principal is satisfied
without any role impl. The first-order equality model is reused to isolate
selection and dictionary timing. `box` is a structural carrier in these
examples; nominal-type elaboration is not being claimed.
-/

namespace Yulang.FrozenMethodExamples

open Inference (Model Comp CompTerm TyTerm)
open RoleConstraints QualifiedInference MethodResolution FrozenMethods

def sizeName : Nat := 20
def sizeRole : Nat := 21
def sizeDeclaration : Nat := 22

def sizeScope : Scope :=
  ⟨[sizeRole], fun role name =>
    if role = sizeRole ∧ name = sizeName then some sizeDeclaration else none⟩

def unknownSite : Site Unit := ⟨sizeName, sizeScope, none, .missing⟩

def boxShape : StructuralBase.Ty Unit := .record sizeName (.base .int) .emptyRecord

def knownSite : Site Unit := { unknownSite with receiver := some boxShape }

def unknownDot : FrozenDot := ⟨.role sizeRole sizeDeclaration, .var 0⟩
def knownDot : FrozenDot := ⟨.field sizeName, .var 0⟩

theorem unknown_selects_role : finalize unknownSite (.var 0) = some unknownDot := by decide
theorem same_scc_known_selects_field : finalize knownSite (.var 0) = some knownDot := by decide

example : freeze { unknownSite with scope := { sizeScope with visibleRoles := [sizeRole, sizeRole] } } =
    some (.role sizeRole sizeDeclaration) := by decide

example : freeze { unknownSite with scope := { sizeScope with visibleRoles := [] } } =
    some (.field sizeName) := by decide

def ambiguousScope : Scope :=
  ⟨[sizeRole, 23], fun role name => if name = sizeName then some (role + 1) else none⟩

example : freeze { unknownSite with scope := ambiguousScope } = none := by decide

example : freeze { knownSite with scope := ambiguousScope, typedFallback := .ambiguous } =
    some (.field sizeName) := by decide

abbrev model := QualifiedExamples.model
abbrev noImpls := QualifiedExamples.noImpls

def sizeGoal (type : TyTerm α) : Goal α := ⟨sizeRole, [type]⟩

def sizeMethod : MethodDecl where
  locals := 1
  requirements := [sizeGoal (.var 0)]
  value := .arrow (.var 0) .empty (.base .int) .empty

def methods : MethodTable := fun _ => sizeMethod

def frozenFunction : CoreExpr := .lam unknownDot.body
def knownFunction : CoreExpr := .lam knownDot.body

def sizeInterface : Interface Empty 1 where
  value := .arrow (.var (.inr 0)) .empty (.base .int) .empty
  obligations := sizeMethod.requirements.map (Goal.rename Sum.inr)

def boxTerm : TyTerm Empty := .record sizeName (.base .int) .emptyRecord
def boxType : model.Ty := model.record sizeName (model.base .int) model.emptyRecord
def boxToInt : CompTerm Empty :=
  CompTerm.pure (.arrow boxTerm .empty (.base .int) .empty)

theorem frozen_function_checked_under_dictionary (theory : Theory model) (type : model.Ty) :
    QualifiedInference.Typing model methods (WithEvidence theory [⟨sizeRole, [type]⟩]) [] frozenFunction
      (Comp.pure model (Comp.arrow model (Comp.pure model type) (Comp.pure model (model.base .int)))) := by
  apply QualifiedInference.Typing.lam (a := Comp.pure model type)
    (b := Comp.pure model (model.base .int))
  · apply QualifiedInference.Typing.app (a := Comp.pure model type)
      (b := Comp.pure model (model.base .int)) (ef := ())
    · apply QualifiedInference.Typing.method (fun _ => type)
      · simp [methods, sizeMethod, sizeGoal, typeEnv, Goal.eval, Predicate.map,
          TyTerm.eval, Comp.pure, Satisfies, WithEvidence]
      · exact ⟨rfl, trivial⟩
    · exact .var rfl (.mono ⟨rfl, trivial⟩)
    · exact ⟨rfl, trivial⟩
  · exact ⟨rfl, trivial⟩

/-- Selection does not eagerly require a concrete impl at definition time. -/
theorem unused_frozen_definition_without_impl :
    (qualifiedLetConstraints methods [] sizeInterface frozenFunction (.lit .unit)
      (CompTerm.pure (.base .unit))).Holds model noImpls Empty.elim := by
  apply (qualified_let_exact model methods noImpls [] [] Empty.elim
    (fun theory => QualifiedInference.EnvRel.nil model theory Empty.elim)
    sizeInterface frozenFunction (.lit .unit) _).mpr
  apply QualifiedLetTyping.intro
  · rfl
  · change Satisfies noImpls []
    simp [Satisfies]
  · intro ι
    exact frozen_function_checked_under_dictionary noImpls (ι 0).1
  · exact .lit ⟨rfl, trivial⟩

/-- At this caller the stored scheme needs precisely `Size box`, despite the
existing `size` field. Its qualifier has not turned into a record constraint. -/
theorem stored_scheme_box_exact (theory : Theory model) :
    (sizeInterface.scheme.instantiate boxToInt).Holds model theory Empty.elim ↔
      theory ⟨sizeRole, [boxType]⟩ := by
  rw [QualifiedInference.Scheme.holds_instantiate, Interface.scheme_exact]
  constructor
  · intro typed
    cases typed with
    | qualified ι requirements subtype =>
        have same : (ι 0).1 = boxType := by
          have types := subtype.1
          change Roles.Term.app 11 [(ι 0).1, model.base .int] =
            Roles.Term.app 11 [boxType, model.base .int] at types
          exact (List.cons.inj (Roles.Term.app.inj types).2).1
        change Satisfies theory [⟨sizeRole, [(ι 0).1]⟩] at requirements
        rw [same] at requirements
        exact requirements _ (by simp)
  · intro evidence
    apply QualifiedInference.BindingTyping.qualified (fun _ => Comp.pure model boxType)
    · change Satisfies theory [⟨sizeRole, [boxType]⟩]
      intro goal member
      have same : goal = ⟨sizeRole, [boxType]⟩ := by simpa using member
      exact same ▸ evidence
    · exact ⟨rfl, trivial⟩

theorem caller_with_field_without_size_impl_rejected :
    ¬ (sizeInterface.scheme.instantiate boxToInt).Holds model noImpls Empty.elim := by
  rw [stored_scheme_box_exact]
  exact QualifiedExamples.no_concrete_evidence _

/-- This also follows for the actual body principal, independently of the
explicit interface used to store the qualified function. -/
theorem generated_frozen_principal_rejects_box :
    ¬ ((QualifiedInference.principal methods ([] : SchemeEnv Empty) frozenFunction).instantiate
      boxToInt).Holds model noImpls Empty.elim := by
  intro generated
  rw [QualifiedInference.Scheme.holds_instantiate] at generated
  have typed := (QualifiedInference.principal_exact model methods noImpls frozenFunction [] []
    Empty.elim (QualifiedInference.EnvRel.nil model noImpls Empty.elim) _).mp generated
  cases typed with
  | lam body _ =>
      cases body with
      | app method _ _ =>
          cases method with
          | method ι requirements _ =>
              change Satisfies noImpls [⟨sizeRole, [ι (0 : Fin 1)]⟩] at requirements
              have demand := requirements ⟨sizeRole, [ι (0 : Fin 1)]⟩ (by simp)
              exact QualifiedExamples.no_concrete_evidence _ demand

theorem same_scc_known_function_typed_without_impl :
    QualifiedInference.Typing model methods noImpls [] knownFunction (boxToInt.eval model Empty.elim) := by
  apply QualifiedInference.Typing.lam (a := Comp.pure model boxType)
    (b := Comp.pure model (model.base .int))
  · apply QualifiedInference.Typing.field (a := model.base .int) (er := ())
    · exact .var rfl (.mono ⟨rfl, trivial⟩)
    · exact ⟨rfl, trivial⟩
  · exact ⟨rfl, trivial⟩

theorem generated_same_scc_known_principal_accepts_box :
    ((QualifiedInference.principal methods ([] : SchemeEnv Empty) knownFunction).instantiate boxToInt).Holds
      model noImpls Empty.elim := by
  rw [QualifiedInference.Scheme.holds_instantiate]
  exact (QualifiedInference.principal_exact model methods noImpls knownFunction [] []
    Empty.elim (QualifiedInference.EnvRel.nil model noImpls Empty.elim) _).mpr
    same_scc_known_function_typed_without_impl

/-- The two SCC-final choices have observably different generated solutions,
although their eventual receiver type is the same record-shaped box. -/
theorem fixed_selection_changes_acceptance :
    finalize unknownSite (.var 0) = some unknownDot ∧
    finalize knownSite (.var 0) = some knownDot ∧
    ¬ ((QualifiedInference.principal methods ([] : SchemeEnv Empty) frozenFunction).instantiate
      boxToInt).Holds model noImpls Empty.elim ∧
    ((QualifiedInference.principal methods ([] : SchemeEnv Empty) knownFunction).instantiate
      boxToInt).Holds model noImpls Empty.elim :=
  ⟨unknown_selects_role, same_scc_known_selects_field, generated_frozen_principal_rejects_box,
    generated_same_scc_known_principal_accepts_box⟩

end Yulang.FrozenMethodExamples
