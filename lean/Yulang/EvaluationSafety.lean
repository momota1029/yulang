import Yulang.EvaluationOrder

/-!
# Computed reads through arbitrary module closures

Spec §2.1 (decision 23, 2026-11-05). A call whose function is not determined
syntactically may read every computed binding mentioned in a module function
body, transitively through named bindings. This finite approximation does not
track closure identity. Both declarations and module statements contribute
lambda bodies. Ordinary lambda construction remains delayed.

The operational layer below uses ordinary captured environments, stored pairs,
projection, application, and Boolean branches. Computed globals are read from
a store; noncomputed declarations are values expanded without an initialization
event. The store may contain future computed values: no ordering/safety premise
is put into evaluation. Its sole closed-module premise is that stored closures
originate in this module's syntax. The checker is proved sound for operational
read prefixes, including a prefix of an evaluation that later diverges.

This is a resolved finite core. Source name resolution, mutable stores, foreign
closures, and source elaboration are separate obligations.
-/

namespace Yulang.EvaluationSafety

open EvaluationOrder FiniteReachability

structure Module (n : Nat) where
  program : Program n
  statements : List (Statement n)

def Module.code (world : Module n) : List (Expr n) :=
  (List.finRange n).map world.program.body ++ world.statements.map Statement.expression

/-- Every syntactic global reference, including those under lambdas. -/
def allReferences : Expr n → List (Fin n)
  | .bound _ | .lit | .bool _ => []
  | .reference name => [name]
  | .lam body | .fst body | .snd body => allReferences body
  | .app left right | .pair left right => allReferences left ++ allReferences right
  | .branch condition yes no =>
      allReferences condition ++ allReferences yes ++ allReferences no

/-- References inside all function bodies, including anonymous/nested lambdas. -/
def functionReferences : Expr n → List (Fin n)
  | .bound _ | .reference _ | .lit | .bool _ => []
  | .lam body => allReferences body
  | .fst pair | .snd pair => functionReferences pair
  | .app left right | .pair left right => functionReferences left ++ functionReferences right
  | .branch condition yes no =>
      functionReferences condition ++ functionReferences yes ++ functionReferences no

def Module.fallback (world : Module n) : List (Fin n) :=
  world.code.flatMap functionReferences

inductive Subexpression : Expr n → Expr n → Prop where
  | refl : Subexpression expression expression
  | lam : Subexpression expression body → Subexpression expression (.lam body)
  | appLeft : Subexpression expression fn → Subexpression expression (.app fn arg)
  | appRight : Subexpression expression arg → Subexpression expression (.app fn arg)
  | pairLeft : Subexpression expression left → Subexpression expression (.pair left right)
  | pairRight : Subexpression expression right → Subexpression expression (.pair left right)
  | fst : Subexpression expression pair → Subexpression expression (.fst pair)
  | snd : Subexpression expression pair → Subexpression expression (.snd pair)
  | condition : Subexpression expression condition → Subexpression expression (.branch condition yes no)
  | yes : Subexpression expression yes → Subexpression expression (.branch condition yes no)
  | no : Subexpression expression no → Subexpression expression (.branch condition yes no)

theorem Subexpression.trans (first : Subexpression a b) (second : Subexpression b c) :
    Subexpression a c := by
  induction second with
  | refl => exact first
  | lam _ ih => exact .lam ih
  | appLeft _ ih => exact .appLeft ih
  | appRight _ ih => exact .appRight ih
  | pairLeft _ ih => exact .pairLeft ih
  | pairRight _ ih => exact .pairRight ih
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | condition _ ih => exact .condition ih
  | yes _ ih => exact .yes ih
  | no _ ih => exact .no ih

theorem Subexpression.references (sub : Subexpression a b) :
    ∀ target ∈ allReferences a, target ∈ allReferences b := by
  induction sub <;> simp_all [allReferences]

theorem function_body_references (sub : Subexpression (.lam body) expression) :
    ∀ target ∈ allReferences body, target ∈ functionReferences expression := by
  induction sub with
  | refl => exact fun _ member => member
  | lam sub _ =>
      intro target member
      exact sub.references target member
  | appLeft _ ih | pairLeft _ ih =>
      intro target member
      exact List.mem_append_left _ (ih target member)
  | appRight _ ih | pairRight _ ih =>
      intro target member
      exact List.mem_append_right _ (ih target member)
  | fst _ ih | snd _ ih => exact ih
  | condition _ ih =>
      intro target member
      exact List.mem_append_left _ (List.mem_append_left _ (ih target member))
  | yes _ ih =>
      intro target member
      exact List.mem_append_left _ (List.mem_append_right _ (ih target member))
  | no _ ih =>
      intro target member
      exact List.mem_append_right _ (ih target member)

def Within (world : Module n) (expression : Expr n) : Prop :=
  ∃ root ∈ world.code, Subexpression expression root

theorem Within.subexpression (inside : Within world outer) (sub : Subexpression inner outer) :
    Within world inner := by
  rcases inside with ⟨root, present, nested⟩
  exact ⟨root, present, sub.trans nested⟩

theorem declaration_within (world : Module n) (name : Fin n) :
    Within world (world.program.body name) := by
  refine ⟨world.program.body name, ?_, .refl⟩
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨name, by simp, rfl⟩

theorem statement_within (world : Module n) (statement : Statement n)
    (present : statement ∈ world.statements) : Within world statement.expression := by
  refine ⟨statement.expression, ?_, .refl⟩
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨statement, present, rfl⟩

theorem function_reference_in_fallback (world : Module n) (body : Expr n)
    (origin : Within world (.lam body)) (target : Fin n)
    (reference : target ∈ allReferences body) : target ∈ world.fallback := by
  rcases origin with ⟨root, present, sub⟩
  exact List.mem_flatMap.mpr ⟨root, present, function_body_references sub target reference⟩

/-- Only a directly named lambda declaration or an immediate lambda determines
its callee. Aliases, computed functions, projections, parameters, and returned
functions use the module-wide fallback. -/
def knownCallee (program : Program n) : Expr n → Bool
  | .lam _ => true
  | .reference name => match program.body name with | .lam _ => true | _ => false
  | _ => false

/-- Conservative invocation summary of a named declaration. -/
def fullSeeds (world : Module n) : Expr n → List (Fin n)
  | .bound _ | .lit | .bool _ => []
  | .reference name => [name]
  | .lam body | .fst body | .snd body => fullSeeds world body
  | .app fn arg => fullSeeds world fn ++ fullSeeds world arg ++
      (if knownCallee world.program fn then [] else world.fallback)
  | .pair left right => fullSeeds world left ++ fullSeeds world right
  | .branch condition yes no =>
      fullSeeds world condition ++ fullSeeds world yes ++ fullSeeds world no

/-- Immediate evaluation seeds; constructing a lambda adds no dependency. -/
def activeSeeds (world : Module n) : Expr n → List (Fin n)
  | .bound _ | .lit | .bool _ | .lam _ => []
  | .reference name => [name]
  | .fst pair | .snd pair => activeSeeds world pair
  | .app fn arg => activeSeeds world fn ++ activeSeeds world arg ++
      (match fn with
        | .lam body => activeSeeds world body
        | _ => if knownCallee world.program fn then [] else world.fallback)
  | .pair left right => activeSeeds world left ++ activeSeeds world right
  | .branch condition yes no =>
      activeSeeds world condition ++ activeSeeds world yes ++ activeSeeds world no

def callSeeds (world : Module n) : Expr n → List (Fin n)
  | .lam body => activeSeeds world body
  | fn => if knownCallee world.program fn then [] else world.fallback

theorem activeSeeds_app (world : Module n) (fn arg : Expr n) :
    activeSeeds world (.app fn arg) =
      activeSeeds world fn ++ activeSeeds world arg ++ callSeeds world fn := by
  cases fn <;> rfl

theorem knownCallee_exact (program : Program n) (fn : Expr n) :
    knownCallee program fn = true ↔
      (∃ body, fn = .lam body) ∨
      (∃ name body, fn = .reference name ∧ program.body name = .lam body) := by
  cases fn with
  | reference name => cases shape : program.body name <;> simp [knownCallee, shape]
  | _ => simp [knownCallee]

theorem unknown_callSeeds (world : Module n) (fn : Expr n)
    (unknown : knownCallee world.program fn = false) : callSeeds world fn = world.fallback := by
  cases fn <;> simp_all [knownCallee, callSeeds]

theorem activeSeeds_subset_fullSeeds (world : Module n) (expression : Expr n) :
    ∀ target ∈ activeSeeds world expression, target ∈ fullSeeds world expression := by
  fun_induction activeSeeds world expression
  case case8 fn arg ihf iha ihbody =>
    intro target member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ (List.mem_append_left _ (ihf target member))
      · exact List.mem_append_left _ (List.mem_append_right _ (iha target member))
    · cases fn with
      | lam body =>
          exact List.mem_append_left _ (List.mem_append_left _ (ihbody target member))
      | _ => exact List.mem_append_right _ member
  case case9 left right ihl ihr =>
    intro target member
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (ihl target member)
    · exact List.mem_append_right _ (ihr target member)
  case case10 condition yes no ihc ihy ihn =>
    intro target member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact List.mem_append_left _ (List.mem_append_left _ (ihc target member))
      · exact List.mem_append_left _ (List.mem_append_right _ (ihy target member))
    · exact List.mem_append_right _ (ihn target member)
  all_goals simp_all [fullSeeds]

theorem fullSeeds_supported (world : Module n) (expression : Expr n) (allowed : Fin n → Prop)
    (references : ∀ target ∈ allReferences expression, allowed target)
    (fallback : ∀ target ∈ world.fallback, allowed target) :
    ∀ target ∈ fullSeeds world expression, allowed target := by
  induction expression with
  | bound _ | lit | bool _ => simp [fullSeeds]
  | reference _ => exact references
  | lam body ih | fst body ih | snd body ih => exact ih references
  | pair left right ihl ihr =>
      intro target member
      rcases List.mem_append.mp member with member | member
      · exact ihl (fun t h => references t (List.mem_append_left _ h)) target member
      · exact ihr (fun t h => references t (List.mem_append_right _ h)) target member
  | branch condition yes no ihc ihy ihn =>
      intro target member
      simp only [fullSeeds, List.mem_append] at member
      rcases member with (member | member) | member
      · exact ihc (fun t h => references t (List.mem_append_left _ (List.mem_append_left _ h))) target member
      · exact ihy (fun t h => references t (List.mem_append_left _ (List.mem_append_right _ h))) target member
      · exact ihn (fun t h => references t (List.mem_append_right _ h)) target member
  | app fn arg ihf iha =>
      intro target member
      simp only [fullSeeds, List.mem_append] at member
      rcases member with (member | member) | member
      · exact ihf (fun t h => references t (List.mem_append_left _ h)) target member
      · exact iha (fun t h => references t (List.mem_append_right _ h)) target member
      · cases knownCallee world.program fn <;> simp_all

def Module.graph (world : Module n) : Adj n := fun name => fullSeeds world (world.program.body name)

def Needed (world : Module n) (expression : Expr n) (target : Fin n) : Prop :=
  Reach world.graph (activeSeeds world expression) target

def dependencies (world : Module n) (expression : Expr n) : Fin n → Bool :=
  closure world.graph (activeSeeds world expression)

theorem dependencies_exact (world : Module n) (expression : Expr n) (target : Fin n) :
    dependencies world expression target = true ↔ Needed world expression target :=
  closure_exact _ _ _

def OrderedAt (world : Module n) (position : Nat) (expression : Expr n) : Prop :=
  ∀ target, Needed world expression target → world.program.computed target = true →
    world.program.position target < position

def checkAt (world : Module n) (position : Nat) (expression : Expr n) : Bool :=
  (List.finRange n).all fun target =>
    decide (dependencies world expression target = true → world.program.computed target = true →
      world.program.position target < position)

theorem checkAt_exact (world : Module n) (position : Nat) (expression : Expr n) :
    checkAt world position expression = true ↔ OrderedAt world position expression := by
  simp only [checkAt, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, dependencies_exact, OrderedAt]

def Ordered (world : Module n) : Prop :=
  (∀ name, world.program.computed name = true →
    OrderedAt world (world.program.position name) (world.program.body name)) ∧
  (∀ statement ∈ world.statements, OrderedAt world statement.position statement.expression)

def check (world : Module n) : Bool :=
  (List.finRange n).all (fun name => decide (world.program.computed name = true →
    checkAt world (world.program.position name) (world.program.body name) = true)) &&
  world.statements.all (fun statement => checkAt world statement.position statement.expression)

theorem check_exact (world : Module n) : check world = true ↔ Ordered world := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, checkAt_exact, Ordered]

@[simp] theorem checkAt_lambda (world : Module n) (position : Nat) (body : Expr n) :
    checkAt world position (.lam body) = true := by
  apply (checkAt_exact _ _ _).mpr
  intro target dependency
  exact False.elim (Reach.no_seed dependency)

/-- Logical support by a set closed under named-declaration dependencies. -/
def Supported (world : Module n) (allowed : Fin n → Prop) (expression : Expr n) : Prop :=
  ∀ target ∈ activeSeeds world expression, allowed target

def GraphClosed (world : Module n) (allowed : Fin n → Prop) : Prop :=
  ∀ source, allowed source → ∀ target ∈ world.graph source, allowed target

theorem Supported.app_parts (support : Supported world allowed (.app fn arg)) :
    Supported world allowed fn ∧ Supported world allowed arg ∧
      (∀ target ∈ callSeeds world fn, allowed target) := by
  unfold Supported at support ⊢
  rw [activeSeeds_app] at support
  exact ⟨fun t h => support t (List.mem_append_left _ (List.mem_append_left _ h)),
    fun t h => support t (List.mem_append_left _ (List.mem_append_right _ h)),
    fun t h => support t (List.mem_append_right _ h)⟩

theorem Supported.named_body (closed : GraphClosed world allowed)
    (support : Supported world allowed (.reference name)) :
    Supported world allowed (world.program.body name) := by
  intro target member
  exact closed name (support name (by simp [activeSeeds])) target
    (activeSeeds_subset_fullSeeds world _ target member)

theorem Supported.function_body (world : Module n) (allowed : Fin n → Prop) (body : Expr n)
    (origin : Within world (.lam body))
    (fallback : ∀ target ∈ world.fallback, allowed target) : Supported world allowed body := by
  intro target member
  apply fullSeeds_supported world body allowed _ fallback target
    (activeSeeds_subset_fullSeeds world body target member)
  intro reference present
  exact fallback reference (function_reference_in_fallback world body origin reference present)

end Yulang.EvaluationSafety
