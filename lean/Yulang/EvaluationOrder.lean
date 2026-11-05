import Yulang.FiniteReachability

/-!
# Conservative evaluation dependencies and source order

This is a finite, name-resolved dependency calculus for declarations and module
statements. Local binders and global declaration identifiers are distinct. A
global function mentioned in an evaluated position is conservatively invoked,
even when passed as an argument. Its summary recursively opens lambdas in result
positions, including lambdas returned through branches or callee expressions.
Arguments, conditions, and pair components retain ordinary value demand.
Constructing an ordinary lambda does not inspect its body;
syntactically applying a lambda does inspect it, including curried applications.

`Depends` is an independent inductive judgement. The executable checker uses
finite graph closure and is exact for that judgement. Acceptance requires every
reached computed declaration to precede the evaluation site strictly. There is
no depth cutoff, topological reordering, or acyclicity assumption on functions.

This is the direct dependency layer. `EvaluationSafety` adds decision 23's
module-wide unnamed-call fallback, and `EvaluationReads` proves that strengthened
checker contains actual closure/argument/stored-pair read prefixes. Initialization
uses both checks. Source name resolution and elaboration are still separate;
constructing a delayed lambda is not a proof that a caller will never invoke it.
-/

namespace Yulang.EvaluationOrder

open FiniteReachability

inductive Expr (n : Nat) where
  | bound : Nat → Expr n
  | reference : Fin n → Expr n
  | lit : Expr n
  | bool : Bool → Expr n
  | lam : Expr n → Expr n
  | app : Expr n → Expr n → Expr n
  | pair : Expr n → Expr n → Expr n
  | fst : Expr n → Expr n
  | snd : Expr n → Expr n
  | branch : Expr n → Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

def Expr.isValue : Expr n → Bool
  | .bound _ | .reference _ | .lit | .bool _ | .lam _ => true
  | .pair left right => left.isValue && right.isValue
  | .app _ _ | .fst _ | .snd _ | .branch _ _ _ => false

/-- The complete syntactic parameter list of a named function. -/
def Expr.arity : Expr n → Nat
  | .lam body => body.arity + 1
  | _ => 0

/-- `calls` opens only lambdas immediately demanded by enclosing applications.
Named global functions are followed separately by the dependency graph. -/
def Expr.references : Expr n → Nat → List (Fin n)
  | .bound _, _ | .lit, _ | .bool _, _ => []
  | .reference name, _ => [name]
  | .lam _, 0 => []
  | .lam body, calls + 1 => body.references calls
  | .app fn arg, calls => fn.references (calls + 1) ++ arg.references 0
  | .pair left right, _ => left.references 0 ++ right.references 0
  | .fst operand, _ | .snd operand, _ => operand.references 0
  | .branch condition yes no, calls =>
      condition.references 0 ++ yes.references calls ++ no.references calls

/-- A syntax-directed relation, without lists or the graph algorithm. -/
def Uses : Expr n → Nat → Fin n → Prop
  | .bound _, _, _ | .lit, _, _ | .bool _, _, _ => False
  | .reference name, _, target => target = name
  | .lam _, 0, _ => False
  | .lam body, calls + 1, target => Uses body calls target
  | .app fn arg, calls, target => Uses fn (calls + 1) target ∨ Uses arg 0 target
  | .pair left right, _, target => Uses left 0 target ∨ Uses right 0 target
  | .fst pair, _, target | .snd pair, _, target => Uses pair 0 target
  | .branch condition yes no, calls, target =>
      (Uses condition 0 target ∨ Uses yes calls target) ∨ Uses no calls target

theorem references_exact (expression : Expr n) (calls : Nat) (target : Fin n) :
    target ∈ expression.references calls ↔ Uses expression calls target := by
  induction expression generalizing calls with
  | bound _ => simp [Expr.references, Uses]
  | reference _ => simp [Expr.references, Uses]
  | lit => simp [Expr.references, Uses]
  | bool _ => simp [Expr.references, Uses]
  | lam body ih => cases calls <;> simp [Expr.references, Uses, ih]
  | app fn arg ihfn iharg => simp [Expr.references, Uses, ihfn, iharg]
  | pair left right ihleft ihright => simp [Expr.references, Uses, ihleft, ihright]
  | fst pair ih | snd pair ih => simp [Expr.references, Uses, ih]
  | branch condition yes no ihc ihy ihn => simp [Expr.references, Uses, ihc, ihy, ihn, or_assoc]

/-- A named function is conservatively followed through every syntactic result
lambda, even when a branch returns it. This summary does not propagate closure
values through local parameters, argument substitution, or pair projection. -/
def Expr.invokedReferences : Expr n → List (Fin n)
  | .bound _ | .lit | .bool _ => []
  | .reference name => [name]
  | .lam body => body.invokedReferences
  | .app fn arg => fn.invokedReferences ++ arg.references 0
  | .pair left right => left.references 0 ++ right.references 0
  | .fst operand | .snd operand => operand.references 0
  | .branch condition yes no =>
      condition.references 0 ++ yes.invokedReferences ++ no.invokedReferences

/-- Independent declarative summary for invoking a named declaration. Only
result positions recurse with invocation demand; other positions use `Uses`. -/
inductive InvokedUses : Expr n → Fin n → Prop where
  | reference : InvokedUses (.reference name) name
  | lam : InvokedUses body target → InvokedUses (.lam body) target
  | appCallee : InvokedUses fn target → InvokedUses (.app fn arg) target
  | appArgument : Uses arg 0 target → InvokedUses (.app fn arg) target
  | pairLeft : Uses left 0 target → InvokedUses (.pair left right) target
  | pairRight : Uses right 0 target → InvokedUses (.pair left right) target
  | fst : Uses pair 0 target → InvokedUses (.fst pair) target
  | snd : Uses pair 0 target → InvokedUses (.snd pair) target
  | branchCondition : Uses condition 0 target → InvokedUses (.branch condition yes no) target
  | branchYes : InvokedUses yes target → InvokedUses (.branch condition yes no) target
  | branchNo : InvokedUses no target → InvokedUses (.branch condition yes no) target

theorem invokedReferences_exact (expression : Expr n) (target : Fin n) :
    target ∈ expression.invokedReferences ↔ InvokedUses expression target := by
  constructor
  · induction expression with
    | bound _ => simp [Expr.invokedReferences]
    | reference name =>
        simp only [Expr.invokedReferences, List.mem_singleton]
        intro equality
        subst target
        exact .reference
    | lit => simp [Expr.invokedReferences]
    | bool _ => simp [Expr.invokedReferences]
    | lam body ih => exact fun member => .lam (ih member)
    | app fn arg ihfn _ =>
        intro member
        rcases List.mem_append.mp member with member | member
        · exact .appCallee (ihfn member)
        · exact .appArgument ((references_exact _ _ _).mp member)
    | pair left right _ _ =>
        intro member
        rcases List.mem_append.mp member with member | member
        · exact .pairLeft ((references_exact _ _ _).mp member)
        · exact .pairRight ((references_exact _ _ _).mp member)
    | fst pair _ => exact fun member => .fst ((references_exact _ _ _).mp member)
    | snd pair _ => exact fun member => .snd ((references_exact _ _ _).mp member)
    | branch condition yes no _ ihyes ihno =>
        intro member
        have alternatives : target ∈ condition.references 0 ∨
            target ∈ yes.invokedReferences ∨ target ∈ no.invokedReferences := by
          simpa only [Expr.invokedReferences, List.mem_append, or_assoc] using member
        rcases alternatives with member | member | member
        · exact .branchCondition ((references_exact _ _ _).mp member)
        · exact .branchYes (ihyes member)
        · exact .branchNo (ihno member)
  · intro use
    induction use <;> simp_all [Expr.invokedReferences, references_exact]

/-- The invocation summary retains every dependency previously exposed by any
finite number of syntactic applications; it can additionally open returned
lambdas for which the named caller's application count is not retained. -/
theorem InvokedUses.of_uses (expression : Expr n) (calls : Nat) (target : Fin n)
    (use : Uses expression calls target) : InvokedUses expression target := by
  induction expression generalizing calls with
  | bound _ => exact False.elim use
  | reference name =>
      have equality : target = name := use
      subst target
      exact .reference
  | lit => exact False.elim use
  | bool _ => exact False.elim use
  | lam body ih =>
      cases calls with
      | zero => exact False.elim use
      | succ calls => exact .lam (ih calls use)
  | app fn arg ihfn _ =>
      rcases use with use | use
      · exact .appCallee (ihfn _ use)
      · exact .appArgument use
  | pair left right _ _ =>
      rcases use with use | use
      · exact .pairLeft use
      · exact .pairRight use
  | fst pair _ => exact .fst use
  | snd pair _ => exact .snd use
  | branch condition yes no _ ihyes ihno =>
      rcases use with (use | use) | use
      · exact .branchCondition use
      · exact .branchYes (ihyes _ use)
      · exact .branchNo (ihno _ use)

structure Program (n : Nat) where
  body : Fin n → Expr n
  position : Fin n → Nat

def Program.computed (program : Program n) (binding : Fin n) : Bool :=
  !(program.body binding).isValue

def Program.graph (program : Program n) : Adj n :=
  fun binding => (program.body binding).invokedReferences

inductive Depends (program : Program n) (root : Expr n) : Fin n → Prop where
  | direct : Uses root 0 target → Depends program root target
  | through : Depends program root source →
      InvokedUses (program.body source) target →
      Depends program root target

theorem depends_iff_reach (program : Program n) (root : Expr n) (target : Fin n) :
    Depends program root target ↔ Reach program.graph (root.references 0) target := by
  constructor
  · intro dependency
    induction dependency with
    | direct use => exact .seed ((references_exact _ _ _).mpr use)
    | through _ use ih => exact .step ih ((invokedReferences_exact _ _).mpr use)
  · intro path
    induction path with
    | seed member => exact .direct ((references_exact _ _ _).mp member)
    | step _ edge ih => exact .through ih ((invokedReferences_exact _ _).mp edge)

def dependencies (program : Program n) (root : Expr n) : Fin n → Bool :=
  closure program.graph (root.references 0)

theorem dependencies_exact (program : Program n) (root : Expr n) (target : Fin n) :
    dependencies program root target = true ↔ Depends program root target := by
  rw [depends_iff_reach]
  exact closure_exact _ _ _

def OrderedAt (program : Program n) (position : Nat) (root : Expr n) : Prop :=
  ∀ target, Depends program root target → program.computed target = true →
    program.position target < position

/-- Only computed bindings impose an initialization-order restriction. -/
def checkAt (program : Program n) (position : Nat) (root : Expr n) : Bool :=
  (List.finRange n).all fun target =>
    decide (dependencies program root target = true → program.computed target = true →
      program.position target < position)

theorem checkAt_exact (program : Program n) (position : Nat) (root : Expr n) :
    checkAt program position root = true ↔ OrderedAt program position root := by
  simp only [checkAt, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, dependencies_exact, OrderedAt]

structure Statement (n : Nat) where
  position : Nat
  expression : Expr n

def Ordered (program : Program n) (statements : List (Statement n)) : Prop :=
  (∀ binding, program.computed binding = true →
    OrderedAt program (program.position binding) (program.body binding)) ∧
  (∀ statement ∈ statements, OrderedAt program statement.position statement.expression)

def check (program : Program n) (statements : List (Statement n)) : Bool :=
  (List.finRange n).all (fun binding => decide (program.computed binding = true →
    checkAt program (program.position binding) (program.body binding) = true)) &&
  statements.all (fun statement => checkAt program statement.position statement.expression)

theorem check_exact (program : Program n) (statements : List (Statement n)) :
    check program statements = true ↔ Ordered program statements := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq, checkAt_exact, Ordered]

theorem rejected_iff (program : Program n) (statements : List (Statement n)) :
    check program statements = false ↔ ¬ Ordered program statements := by
  cases result : check program statements <;> simp_all [← check_exact]

/-- Every computed reference required at this site has already been initialized
in the unchanged source order. Pure values require no initialization event. -/
def AvailableBefore (program : Program n) (position : Nat) (target : Fin n) : Prop :=
  program.computed target = false ∨ program.position target < position

theorem accepted_references_available (program : Program n) (position : Nat) (root : Expr n)
    (accepted : checkAt program position root = true) :
    ∀ target, Depends program root target → AvailableBefore program position target := by
  intro target dependency
  cases computed : program.computed target with
  | false => exact Or.inl computed
  | true => exact Or.inr ((checkAt_exact _ _ _).mp accepted target dependency computed)

theorem accepted_initializer_earlier (program : Program n) (statements : List (Statement n))
    (accepted : check program statements = true) (source target : Fin n)
    (sourceComputed : program.computed source = true)
    (dependency : Depends program (program.body source) target)
    (targetComputed : program.computed target = true) :
    program.position target < program.position source :=
  ((check_exact _ _).mp accepted).1 source sourceComputed target dependency targetComputed

theorem accepted_statement_available (program : Program n) (statements : List (Statement n))
    (accepted : check program statements = true) (statement : Statement n)
    (present : statement ∈ statements) (target : Fin n)
    (dependency : Depends program statement.expression target) :
    AvailableBefore program statement.position target := by
  apply accepted_references_available program statement.position statement.expression
  · exact (checkAt_exact _ _ _).mpr (((check_exact _ _).mp accepted).2 statement present)
  · exact dependency

theorem computed_self_dependency_rejected (program : Program n)
    (statements : List (Statement n)) (binding : Fin n)
    (computed : program.computed binding = true)
    (cycle : Depends program (program.body binding) binding) :
    check program statements = false := by
  apply (rejected_iff _ _).mpr
  intro ordered
  exact Nat.lt_irrefl _ (ordered.1 binding computed binding cycle computed)

theorem future_computed_dependency_rejected (program : Program n)
    (statements : List (Statement n)) (source target : Fin n)
    (sourceComputed : program.computed source = true)
    (targetComputed : program.computed target = true)
    (dependency : Depends program (program.body source) target)
    (future : program.position source ≤ program.position target) :
    check program statements = false := by
  apply (rejected_iff _ _).mpr
  intro ordered
  exact Nat.not_lt_of_ge future (ordered.1 source sourceComputed target dependency targetComputed)

/-- A lambda value has no immediate global dependency, even if its body is cyclic. -/
theorem lambda_no_dependency (program : Program n) (body : Expr n) (target : Fin n) :
    ¬ Depends program (.lam body) target := by
  rw [depends_iff_reach]
  exact Reach.no_seed

@[simp] theorem checkAt_lambda (program : Program n) (position : Nat) (body : Expr n) :
    checkAt program position (.lam body) = true := by
  apply (checkAt_exact _ _ _).mpr
  intro target dependency
  exact False.elim (lambda_no_dependency program body target dependency)

/-- Delay does not erase a dependency once the lambda is syntactically called. -/
theorem applied_lambda_preserves_body_dependency (program : Program n)
    (body argument : Expr n) (target : Fin n)
    (dependency : Depends program body target) :
    Depends program (.app (.lam body) argument) target := by
  induction dependency with
  | direct use => exact .direct (Or.inl use)
  | through _ use ih => exact .through ih use

/-- Mentioning a named function as an argument follows its complete invocation
summary, including lambdas returned through branch result positions. -/
theorem passed_function_invoked_dependency (program : Program n) (fn : Expr n)
    (name target : Fin n)
    (bodyUse : InvokedUses (program.body name) target) :
    Depends program (.app fn (.reference name)) target :=
  .through (.direct (Or.inr rfl)) bodyUse

/-- Compatibility with the previous leading-parameter invocation criterion. -/
theorem passed_function_dependency (program : Program n) (fn : Expr n)
    (name target : Fin n)
    (bodyUse : Uses (program.body name) (program.body name).arity target) :
    Depends program (.app fn (.reference name)) target :=
  passed_function_invoked_dependency program fn name target
    (InvokedUses.of_uses _ _ _ bodyUse)

namespace Examples

/-- `h x = late; k = h (); late = compute ()`. -/
def forward : Program 3 where
  body
    | 0 => .lam (.reference 2)
    | 1 => .app (.reference 0) .lit
    | _ => .app (.lam .lit) .lit
  position := Fin.val

theorem forward_computed_rejected : check forward [] = false := by decide

theorem passing_function_rejected :
    checkAt forward 1 (.app (.lam .lit) (.reference 0)) = false := by decide

theorem function_before_initialization_rejected :
    checkAt forward 1 (.app (.reference 0) .lit) = false := by decide

theorem function_after_initialization_accepted :
    checkAt forward 3 (.app (.reference 0) .lit) = true := by decide

theorem inline_lambda_application_rejected :
    checkAt forward 1 (.app (.lam (.reference 2)) .lit) = false := by decide

theorem curried_inline_lambda_application_rejected :
    checkAt forward 1 (.app (.app (.lam (.lam (.reference 2))) .lit) .lit) = false := by decide

/-- `factory x = if c then (\y -> late) else (\y -> late)` followed by
`k = factory () (); late = compute ()`. Following only leading lambdas misses
`late`, because the branch interrupts the syntactic parameter list. -/
def returnedFactory : Program 3 where
  body
    | 0 => .lam (.branch .lit (.lam (.reference 2)) (.lam (.reference 2)))
    | 1 => .app (.app (.reference 0) .lit) .lit
    | _ => .app (.lam .lit) .lit
  position := Fin.val

theorem returned_lambda_before_initialization_rejected :
    check returnedFactory [] = false := by decide

theorem passing_returned_lambda_factory_rejected :
    checkAt returnedFactory 1 (.app (.lam .lit) (.reference 0)) = false := by decide

theorem returned_lambda_after_initialization_accepted :
    checkAt returnedFactory 3 (.app (.app (.reference 0) .lit) .lit) = true := by decide

theorem wrapping_returned_lambda_factory_delays_dependency :
    checkAt returnedFactory 1 (.lam (.app (.app (.reference 0) .lit) .lit)) = true :=
  checkAt_lambda _ _ _

def delayed : Program 3 where
  body
    | 0 => .lam (.reference 2)
    | 1 => .lam (.app (.reference 0) (.bound 0))
    | _ => .app (.lam .lit) .lit
  position := Fin.val

theorem wrapping_delays_initialization_dependency : check delayed [] = true := by decide

def valueCycle : Program 2 where
  body
    | 0 => .app (.lam (.bound 0)) (.reference 1)
    | _ => .app (.lam (.bound 0)) (.reference 0)
  position := Fin.val

theorem computed_cycle_rejected : check valueCycle [] = false := by decide

def functionCycle : Program 2 where
  body
    | 0 => .lam (.app (.reference 1) (.bound 0))
    | _ => .lam (.app (.reference 0) (.bound 0))
  position := Fin.val

theorem mutual_functions_accepted : check functionCycle [] = true := by decide

theorem pure_function_cycle_does_not_invent_computed_dependency :
    checkAt functionCycle 0 (.app (.reference 0) .lit) = true := by decide

def laterLiteral : Program 2 where
  body
    | 0 => .app (.lam (.bound 0)) (.reference 1)
    | _ => .lit
  position := Fin.val

theorem forward_literal_accepted : check laterLiteral [] = true := by decide

end Examples
end Yulang.EvaluationOrder
