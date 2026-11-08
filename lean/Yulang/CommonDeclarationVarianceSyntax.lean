import Yulang.FiniteHorn

/-!
# Source equations for declaration variance

This is syntax for a finite resolved declaration graph, not a variance table.
Each original parameter has a declaration-body root. Local references retain
finite source positions; a nominal application retains its resolved formal
parameter and the actual argument expression. `barrier` is the function
wrapper boundary. Negative polarity is represented by `true`.

`Derivation` is an independent source occurrence judgment. In eager mode a
function boundary ends the current traversal; in ordinary mode its argument
and result occurrences remain visible. Nominal arguments are used only when
the corresponding callee formal has a derivation, so a phantom recursive
argument cannot bootstrap its own use.
-/

namespace Yulang.CommonDeclarationVarianceSyntax

variable {Index Parameter : Type}

inductive Expr (Index Parameter : Type) where
  | empty
  | parameter : Parameter → Expr Index Parameter
  | reference : Index → Expr Index Parameter
  | both : Expr Index Parameter → Expr Index Parameter → Expr Index Parameter
  | negative : Expr Index Parameter → Expr Index Parameter
  | barrier : Expr Index Parameter → Expr Index Parameter
  | application : Parameter → Expr Index Parameter → Expr Index Parameter

structure Program (Index Parameter : Type) where
  body : Index → Expr Index Parameter
  root : Parameter → Index

abbrev Fact (Index Parameter : Type) := Index × Parameter × Bool

inductive Derivation (program : Program Index Parameter) (eager : Bool) :
    Expr Index Parameter → Parameter → Bool → Prop where
  | parameter (parameter : Parameter) : Derivation program eager (.parameter parameter) parameter false
  | reference : Derivation program eager (program.body index) parameter sign →
      Derivation program eager (.reference index) parameter sign
  | first : Derivation program eager first parameter sign →
      Derivation program eager (.both first last) parameter sign
  | last : Derivation program eager last parameter sign →
      Derivation program eager (.both first last) parameter sign
  | negative : Derivation program eager source parameter sign →
      Derivation program eager (.negative source) parameter (!sign)
  | barrier : eager = false → Derivation program eager source parameter sign →
      Derivation program eager (.barrier source) parameter sign
  | application : Derivation program eager (program.body (program.root formal)) formal direction →
      Derivation program eager actual parameter sign →
      Derivation program eager (.application formal actual) parameter (Bool.xor direction sign)

def Supports (program : Program Index Parameter) (eager : Bool)
    (holds : Fact Index Parameter → Prop) : Expr Index Parameter → Parameter → Bool → Prop
  | .empty, _, _ => False
  | .parameter source, parameter, sign => source = parameter ∧ sign = false
  | .reference index, parameter, sign => holds (index, parameter, sign)
  | .both first last, parameter, sign =>
      Supports program eager holds first parameter sign ∨ Supports program eager holds last parameter sign
  | .negative source, parameter, sign => Supports program eager holds source parameter (!sign)
  | .barrier source, parameter, sign => eager = false ∧ Supports program eager holds source parameter sign
  | .application formal actual, parameter, sign =>
      ∃ direction : Bool, holds (program.root formal, formal, direction) ∧
        Supports program eager holds actual parameter (Bool.xor direction sign)

theorem supports_derivation (program : Program Index Parameter) (eager : Bool)
    (holds : Fact Index Parameter → Prop)
    (sound : ∀ index parameter sign, holds (index, parameter, sign) →
      Derivation program eager (program.body index) parameter sign)
    (expression : Expr Index Parameter) (parameter : Parameter) (sign : Bool) :
    Supports program eager holds expression parameter sign →
      Derivation program eager expression parameter sign := by
  induction expression generalizing sign with
  | empty => exact False.elim
  | parameter source =>
      rintro ⟨rfl, rfl⟩
      exact .parameter _
  | reference index => exact fun premise => .reference (sound _ _ _ premise)
  | both first last ihFirst ihLast =>
      intro supported
      exact supported.elim (fun premise => .first (ihFirst _ premise))
        (fun premise => .last (ihLast _ premise))
  | negative source ih =>
      intro premise
      simpa only [Bool.not_not] using Derivation.negative (ih (!sign) premise)
  | barrier source ih =>
      rintro ⟨mode, premise⟩
      exact .barrier mode (ih _ premise)
  | application formal actual ih =>
      rintro ⟨direction, callee, argument⟩
      have derived := Derivation.application (sound _ _ _ callee) (ih _ argument)
      cases direction <;> cases sign <;> simpa using derived

theorem Derivation.supported (program : Program Index Parameter) (eager : Bool)
    (holds : Fact Index Parameter → Prop)
    (closed : ∀ index parameter sign,
      Supports program eager holds (program.body index) parameter sign → holds (index, parameter, sign))
    {expression : Expr Index Parameter} {parameter : Parameter} {sign : Bool}
    (derived : Derivation program eager expression parameter sign) :
    Supports program eager holds expression parameter sign := by
  induction derived with
  | parameter => exact ⟨rfl, rfl⟩
  | reference premise ih => exact closed _ _ _ ih
  | first premise ih => exact Or.inl ih
  | last premise ih => exact Or.inr ih
  | negative premise ih => simpa only [Supports, Bool.not_not] using ih
  | barrier mode premise ih => exact ⟨mode, ih⟩
  | @application formal direction actual parameter sign callee argument ihCallee ihArgument =>
      refine ⟨direction, closed _ _ _ ihCallee, ?_⟩
      cases direction <;> cases sign <;> simpa using ihArgument

def clauses [DecidableEq Parameter] (program : Program Index Parameter) (eager : Bool) :
    Expr Index Parameter → Parameter → Bool → List (List (Fact Index Parameter))
  | .empty, _, _ => []
  | .parameter source, parameter, sign => if source = parameter ∧ sign = false then [[]] else []
  | .reference index, parameter, sign => [[(index, parameter, sign)]]
  | .both first last, parameter, sign =>
      clauses program eager first parameter sign ++ clauses program eager last parameter sign
  | .negative source, parameter, sign => clauses program eager source parameter (!sign)
  | .barrier source, parameter, sign => if eager then [] else clauses program eager source parameter sign
  | .application formal actual, parameter, sign =>
      (clauses program eager actual parameter sign).map ((program.root formal, formal, false) :: ·) ++
      (clauses program eager actual parameter (!sign)).map ((program.root formal, formal, true) :: ·)

def AnyClause (holds : Fact Index Parameter → Prop) (alternatives : List (List (Fact Index Parameter))) : Prop :=
  ∃ premises ∈ alternatives, ∀ fact ∈ premises, holds fact

private theorem any_append (holds : Fact Index Parameter → Prop) (first last) :
    AnyClause holds (first ++ last) ↔ AnyClause holds first ∨ AnyClause holds last := by
  simp only [AnyClause, List.mem_append]
  constructor
  · rintro ⟨premises, member, valid⟩
    exact member.elim (fun left => Or.inl ⟨premises, left, valid⟩)
      (fun right => Or.inr ⟨premises, right, valid⟩)
  · rintro (⟨premises, member, valid⟩ | ⟨premises, member, valid⟩)
    · exact ⟨premises, Or.inl member, valid⟩
    · exact ⟨premises, Or.inr member, valid⟩

private theorem any_cons (holds : Fact Index Parameter → Prop) (fact) (alternatives) :
    AnyClause holds (alternatives.map (fact :: ·)) ↔ holds fact ∧ AnyClause holds alternatives := by
  simp only [AnyClause, List.mem_map]
  constructor
  · rintro ⟨_, ⟨premises, member, rfl⟩, valid⟩
    exact ⟨valid fact List.mem_cons_self, premises, member,
      fun next present => valid next (List.mem_cons_of_mem _ present)⟩
  · rintro ⟨head, premises, member, valid⟩
    refine ⟨fact :: premises, ⟨premises, member, rfl⟩, ?_⟩
    intro next present
    exact (List.mem_cons.mp present).elim (fun same => same ▸ head) (valid next)

theorem clauses_exact [DecidableEq Parameter] (program : Program Index Parameter) (eager : Bool)
    (holds : Fact Index Parameter → Prop) (expression : Expr Index Parameter)
    (parameter : Parameter) (sign : Bool) :
    AnyClause holds (clauses program eager expression parameter sign) ↔
      Supports program eager holds expression parameter sign := by
  induction expression generalizing sign with
  | empty => simp [clauses, AnyClause, Supports]
  | parameter source =>
      by_cases same : source = parameter ∧ sign = false <;>
        simp [clauses, same, AnyClause, Supports]
  | reference index =>
      change (∃ premises ∈ [[(index, parameter, sign)]], ∀ fact ∈ premises, holds fact) ↔
        holds (index, parameter, sign)
      simp only [List.mem_singleton, exists_eq_left, forall_eq]
  | both first last ihFirst ihLast =>
      simp only [clauses, any_append, Supports, ihFirst, ihLast]
  | negative source ih => exact ih (!sign)
  | barrier source ih =>
      cases eager
      · simpa only [clauses, Supports, Bool.false_eq_true, ↓reduceIte, true_and] using ih sign
      · simp only [clauses, Supports, ↓reduceIte, Bool.true_eq_false, false_and,
          AnyClause, List.not_mem_nil, false_and, exists_false]
  | application formal actual ih =>
      simp only [clauses, any_append, any_cons, ih, Supports]
      constructor
      · rintro (⟨callee, argument⟩ | ⟨callee, argument⟩)
        · exact ⟨false, callee, by simpa using argument⟩
        · exact ⟨true, callee, by simpa using argument⟩
      · rintro ⟨direction, callee, argument⟩
        cases direction
        · exact Or.inl ⟨callee, by simpa using argument⟩
        · exact Or.inr ⟨callee, by simpa using argument⟩

end Yulang.CommonDeclarationVarianceSyntax
