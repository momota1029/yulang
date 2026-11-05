import Yulang.QualifiedGeneralization
import Yulang.ModuleRoles
import Yulang.SignedStructural

/-!
# Non-vacuous dictionary timing examples

This first-order equality model isolates role evidence from structural subtyping.
The general inference theorems quantify over the existing `Inference.Model`;
these examples do not replace the separate structural reference model.
-/

namespace Yulang.QualifiedExamples

open Inference RoleConstraints QualifiedInference

def baseCode : Base → Nat
  | .int => 0
  | .str => 1
  | .bool => 2
  | .unit => 3

def model : Model where
  Ty := Roles.Term
  Row := Unit
  base := fun b => .app (baseCode b) []
  bottom := .app 4 []
  union := fun a b => .app 5 [a, b]
  inter := fun a b => .app 6 [a, b]
  pair := fun a b => .app 7 [a, b]
  emptyRecord := .app 8 []
  record := fun label a b => .app 9 [.app label [], a, b]
  variant := fun label a => .app 10 [.app label [], a]
  arrow := fun a _ b _ => .app 11 [a, b]
  empty := ()
  join := fun _ _ => ()
  subTy := Eq
  subRow := fun _ _ => True

def addGoal (t : TyTerm α) : Goal α := ⟨0, [t]⟩

def addMethod : MethodDecl where
  locals := 1
  requirements := [addGoal (.var 0)]
  value := .arrow (.var 0) .empty (.arrow (.var 0) .empty (.var 0) .empty) .empty

def methods : MethodTable := fun _ => addMethod

def twice : QualifiedInference.Expr :=
  .lam (.app (.app (.method 0) (.var 0)) (.var 0))

/-- The raw obligation is the method's declared predicate, before partitioning. -/
def twiceInterface : Interface Empty 1 where
  value := .arrow (.var (.inr 0)) .empty (.var (.inr 0)) .empty
  obligations := addMethod.requirements.map (Goal.rename Sum.inr)

def decode : model.Ty → Roles.Term := fun t => t

def noImpls : Theory model := resolvingTheory decode []

theorem no_concrete_evidence (goal : Predicate model.Ty) : ¬ noImpls goal :=
  empty_resolver_has_no_evidence _

theorem twice_typed_under_dictionary (theory : Theory model) (t : model.Ty) :
    QualifiedInference.Typing model methods
      (WithEvidence theory [⟨0, [t]⟩]) [] twice
      (Comp.pure model (Comp.arrow model (Comp.pure model t) (Comp.pure model t))) := by
  apply QualifiedInference.Typing.lam (a := Comp.pure model t) (b := Comp.pure model t)
  · apply QualifiedInference.Typing.app (a := Comp.pure model t) (b := Comp.pure model t) (ef := ())
    · apply QualifiedInference.Typing.app (a := Comp.pure model t)
        (b := Comp.pure model (Comp.arrow model (Comp.pure model t) (Comp.pure model t))) (ef := ())
      · apply QualifiedInference.Typing.method (fun _ => t)
        · simp [methods, addMethod, addGoal, typeEnv, Goal.eval, Predicate.map,
            TyTerm.eval, Comp.pure, Satisfies, WithEvidence]
        · exact ⟨rfl, trivial⟩
      · exact .var rfl (.mono ⟨rfl, trivial⟩)
      · exact ⟨rfl, trivial⟩
    · exact .var rfl (.mono ⟨rfl, trivial⟩)
    · exact ⟨rfl, trivial⟩
  · exact ⟨rfl, trivial⟩

/-- Defining and exporting the qualified function needs no visible impl. -/
theorem unused_qualified_definition_without_impl :
    (qualifiedLetConstraints methods [] twiceInterface twice (.lit .unit)
      (CompTerm.pure (.base .unit))).Holds model noImpls Empty.elim := by
  apply (qualified_let_exact model methods noImpls [] [] Empty.elim
    (fun theory => QualifiedInference.EnvRel.nil model theory Empty.elim)
    twiceInterface twice (.lit .unit) _).mpr
  apply QualifiedLetTyping.intro
  · rfl
  · change Satisfies noImpls []
    simp [Satisfies]
  · intro ι
    exact twice_typed_under_dictionary noImpls (ι 0).1
  · exact .lit ⟨rfl, trivial⟩

theorem qualified_binding_without_evidence_rejected (c : Comp model) :
    ¬ QualifiedInference.BindingTyping model noImpls
      (twiceInterface.binding model Empty.elim) c := by
  intro typed
  cases typed with
  | qualified ι requirements _ =>
    change Satisfies noImpls [⟨0, [(ι 0).1]⟩] at requirements
    have demand := requirements ⟨0, [(ι 0).1]⟩ (by simp)
    exact no_concrete_evidence _ demand

/-- Merely using the stored qualified value now demands its dictionary. -/
theorem used_qualified_definition_without_impl_rejected (out : CompTerm Empty) :
    ¬ (qualifiedLetConstraints methods [] twiceInterface twice (.var 0) out).Holds
      model noImpls Empty.elim := by
  intro generated
  have typed := (qualified_let_exact model methods noImpls [] [] Empty.elim
    (fun theory => QualifiedInference.EnvRel.nil model theory Empty.elim)
    twiceInterface twice (.var 0) out).mp generated
  cases typed with
  | intro _ _ _ body =>
    cases body with
    | var lookup evidence =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      cases lookup
      exact qualified_binding_without_evidence_rejected _ evidence

def addIntImpl : Roles.Impl := ⟨0, [.app 0 []], [], 20⟩

theorem addInt_wf : Roles.WellFormed [addIntImpl] := by
  simp [Roles.WellFormed, Roles.Impl.WellFormed, addIntImpl]

def intEvidence : Theory model := resolvingTheory decode [addIntImpl]

theorem add_int_resolves : intEvidence ⟨0, [.app 0 []]⟩ := by
  apply (resolvingTheory_iff (m := model) decode [addIntImpl] addInt_wf _).mpr
  rw [Roles.resolve_one _ _ _ addIntImpl (by decide)]
  rfl

theorem add_str_does_not_resolve : ¬ intEvidence ⟨0, [.app 1 []]⟩ := by
  rw [intEvidence, resolvingTheory_iff (m := model) decode [addIntImpl] addInt_wf]
  rw [Roles.resolve_none _ _ _ (by decide)]
  decide

theorem qualified_use_at_int :
    (twiceInterface.scheme.instantiate
      (CompTerm.pure (.arrow (.base .int) .empty (.base .int) .empty))).Holds
        model intEvidence Empty.elim := by
  rw [QualifiedInference.Scheme.holds_instantiate, Interface.scheme_exact]
  apply QualifiedInference.BindingTyping.qualified (m := model) (theory := intEvidence)
    (fun _ => (Roles.Term.app 0 [], ()))
  · intro goal member
    have eq : goal = ⟨0, [.app 0 []]⟩ := by
      change goal ∈ [⟨0, [Roles.Term.app 0 []]⟩] at member
      simpa using member
    exact eq ▸ add_int_resolves
  · exact ⟨rfl, trivial⟩

/-- A concrete/captured-only obligation is not hidden in an unused scheme. -/
def capturedInterface : Interface Unit 1 where
  value := twiceInterface.value.rename (Sum.map Empty.elim id)
  obligations := [addGoal (.var (.inl ())), addGoal (.var (.inr 0))]

theorem captured_role_stays_pending :
    pending capturedInterface.obligations = [addGoal (.var ())] := rfl

theorem captured_constraint_not_erased (out : CompTerm Unit) :
    ¬ (qualifiedLetConstraints methods [] capturedInterface twice (.lit .unit) out).Holds
      model noImpls (fun _ => (.app 1 [], ())) := by
  intro h
  have typed := (qualified_let_exact model methods noImpls [] [] _
    (fun theory => QualifiedInference.EnvRel.nil model theory _) capturedInterface twice (.lit .unit) out).mp h
  cases typed with
  | intro _ shared _ _ =>
    exact no_concrete_evidence ⟨0, [.app 1 []]⟩ (shared _ (by simp [captured_role_stays_pending,
      addGoal, Goal.eval, Predicate.map, TyTerm.eval]))

/-- A weak captured slot still missing at EOF is rejected, not generalized. -/
theorem eof_rejects_unsolved_weak_slot :
    finishModule model decode [addIntImpl] addInt_wf (fun _ : Unit => none) capturedInterface = none :=
  finishModule_missing model decode [addIntImpl] addInt_wf _ capturedInterface () (by decide) rfl

/-- Later uses may determine the weak slot before the same module ends. -/
theorem eof_accepts_later_integer_solution :
    finishModule model decode [addIntImpl] addInt_wf
      (fun _ : Unit => some (Roles.Term.app 0 [], ())) capturedInterface =
      some (capturedInterface.closeAt model (fun _ => (Roles.Term.app 0 [], ()))) := by
  apply (finishModule_exact model decode [addIntImpl] addInt_wf _ _ _).mpr
  refine ⟨rfl, ?_, rfl⟩
  change Satisfies intEvidence [⟨0, [.app 0 []]⟩]
  intro goal member
  have he : goal = ⟨0, [.app 0 []]⟩ := by simpa using member
  exact he ▸ add_int_resolves

theorem eof_rejects_unsupported_solution :
    finishModule model decode [addIntImpl] addInt_wf
      (fun _ : Unit => some (Roles.Term.app 1 [], ())) capturedInterface = none := by
  have rejected : pendingCheck model decode [addIntImpl] addInt_wf
      (completeAssignment model (fun _ : Unit => some (Roles.Term.app 1 [], ()))) capturedInterface = false := by
    cases h : pendingCheck model decode [addIntImpl] addInt_wf
        (completeAssignment model (fun _ : Unit => some (Roles.Term.app 1 [], ()))) capturedInterface with
    | false => rfl
    | true =>
        have accepted := (pendingCheck_exact model decode [addIntImpl] addInt_wf _ capturedInterface).mp h
        change Satisfies intEvidence [⟨0, [.app 1 []]⟩] at accepted
        exact (add_str_does_not_resolve (accepted _ (by simp))).elim
  simp [finishModule, rejected]

theorem empty_impls_wellFormed : Roles.WellFormed [] := by simp [Roles.WellFormed]

/-- Generalized qualifiers stay in the export; EOF does not demand an impl
for every possible future instantiation of the qualified function. -/
theorem eof_exports_abstract_qualified_function :
    finishModule model decode [] empty_impls_wellFormed (fun e : Empty => nomatch e) twiceInterface =
      some (twiceInterface.closeAt model Empty.elim) := rfl

end Yulang.QualifiedExamples

namespace Yulang.QualifiedRowExamples

open Inference RoleConstraints QualifiedInference

abbrev rowModel := SignedStructural.model 1 Nat

def callback (row : Directed.Row 1 Nat) : rowModel.Ty :=
  .arrow (.base .unit) [] (.base .unit) row

def identityOnCallback (row : Directed.Row 1 Nat) : Comp rowModel :=
  (.arrow (callback row) [] (callback row) [], [])

/-- The generalized row occurs twice inside latent callback result positions. -/
def callbackInterface : Interface Unit 1 where
  value := .arrow
    (.arrow (.base .unit) .empty (.base .unit) (.var (.inr 0))) .empty
    (.arrow (.base .unit) .empty (.base .unit) (.var (.inr 0))) .empty
  obligations := []

theorem independently_instantiates_latent_row (row : Directed.Row 1 Nat) :
    (callbackInterface.scheme.instantiate (CompTerm.var ())).Holds rowModel
      (fun _ => False) (fun _ => identityOnCallback row) := by
  rw [QualifiedInference.Scheme.holds_instantiate, Interface.scheme_exact]
  apply QualifiedInference.BindingTyping.qualified (m := rowModel) (fun _ => (.base .unit, row))
  · simp [callbackInterface, qualifiers, Satisfies]
  · exact ⟨.refl _, SignedStructural.row_refl _⟩

theorem two_nonempty_rows_from_one_scheme :
    (callbackInterface.scheme.instantiate (CompTerm.var ())).Holds rowModel
      (fun _ => False) (fun _ => identityOnCallback [Directed.raw 0]) ∧
    (callbackInterface.scheme.instantiate (CompTerm.var ())).Holds rowModel
      (fun _ => False) (fun _ => identityOnCallback [Directed.raw 1]) :=
  ⟨independently_instantiates_latent_row _, independently_instantiates_latent_row _⟩

theorem example_rows_distinct :
    ([Directed.raw 0] : Directed.Row 1 Nat) ≠ [Directed.raw 1] := by
  intro equal
  have head : Directed.raw (n := 1) 0 = Directed.raw 1 := List.cons.inj equal |>.1
  have key := congrArg Directed.Occurrence.key head
  cases key

end Yulang.QualifiedRowExamples
