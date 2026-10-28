import YulangClosure.HigherOrderSyntax
import YulangClosure.CoreSubstitution

namespace YulangClosure.HigherOrder

mutual
  def renameValue (r : Nat → Nat) : Value → Value
    | .var i => .var (r i)
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (renameComp r m)
    | .inLeft v => .inLeft (renameValue r v)
    | .inRight v => .inRight (renameValue r v)
    | .both v => .both (renameValue r v)
    | .top v => .top (renameValue r v)
    | .view v o => .view (renameValue r v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (renameComp (Original.up r) body) (renameAdapter r consumer)
    | .wrap f input output => .wrap (renameValue r f) (renameAdapter r input) (renameAdapter r output)
  def renameComp (r : Nat → Nat) : Comp → Comp
    | .ret v => .ret (renameValue r v)
    | .force v => .force (renameValue r v)
    | .chooseLeft v => .chooseLeft (renameValue r v)
    | .chooseRight v => .chooseRight (renameValue r v)
    | .absurd v => .absurd (renameValue r v)
    | .bind m n => .bind (renameComp r m) (renameComp (Original.up r) n)
    | .unionCase v l right => .unionCase (renameValue r v) (renameComp (Original.up r) l) (renameComp (Original.up r) right)
    | .scope owner body => .scope owner (renameComp r body)
    | .expose ev rv body => .expose ev rv (renameComp r body)
    | .request op v k => .request op (renameValue r v) (renameComp (Original.up r) k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (renameValue r f) (renameValue r a)
  def renameAdapter (r : Nat → Nat) : Adapter → Adapter
    | .mk a b body paths views => .mk a b (renameComp (Original.up r) body) paths views
end

def lift (s : Nat → Value) : Nat → Value
  | 0 => .var 0
  | n+1 => renameValue Nat.succ (s n)

mutual
  def substValue (s : Nat → Value) : Value → Value
    | .var i => s i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (substComp s m)
    | .inLeft v => .inLeft (substValue s v)
    | .inRight v => .inRight (substValue s v)
    | .both v => .both (substValue s v)
    | .top v => .top (substValue s v)
    | .view v o => .view (substValue s v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (substComp (lift s) body) (substAdapter s consumer)
    | .wrap f input output => .wrap (substValue s f) (substAdapter s input) (substAdapter s output)
  def substComp (s : Nat → Value) : Comp → Comp
    | .ret v => .ret (substValue s v)
    | .force v => .force (substValue s v)
    | .chooseLeft v => .chooseLeft (substValue s v)
    | .chooseRight v => .chooseRight (substValue s v)
    | .absurd v => .absurd (substValue s v)
    | .bind m n => .bind (substComp s m) (substComp (lift s) n)
    | .unionCase v l r => .unionCase (substValue s v) (substComp (lift s) l) (substComp (lift s) r)
    | .scope owner body => .scope owner (substComp s body)
    | .expose ev rv body => .expose ev rv (substComp s body)
    | .request op v k => .request op (substValue s v) (substComp (lift s) k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (substValue s f) (substValue s a)
  def substAdapter (s : Nat → Value) : Adapter → Adapter
    | .mk a b body paths views => .mk a b (substComp (lift s) body) paths views
end

def RenamingTyped (env target : Context) (r : Nat → Nat) : Prop :=
  ∀ i a, env i = some a → target (r i) = some a

theorem up_typed (h : RenamingTyped env target r) (a : Ty) :
    RenamingTyped (extend env a) (extend target a) (Original.up r) := by
  intro i b hi
  cases i with
  | zero => exact hi
  | succ i => exact h i b hi

mutual
  theorem renameValue_typed (h : ValueTyped env v a) (ht : RenamingTyped env target r) :
      ValueTyped target (renameValue r v) a := by
    cases h with
    | var h => exact .var (ht _ _ h)
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (renameComp_typed h ht)
    | inLeft h => exact .inLeft (renameValue_typed h ht)
    | inRight h => exact .inRight (renameValue_typed h ht)
    | top h => exact .top (renameValue_typed h ht)
    | view h => exact .view (renameValue_typed h ht)
    | both h k => exact .both (renameValue_typed h ht) (renameValue_typed k ht)
    | lambdaValue h k => exact .lambdaValue (renameComp_typed h (up_typed ht _)) (renameAdapter_typed k ht)
    | lambdaComputation h k => exact .lambdaComputation (renameComp_typed h (up_typed ht _)) (renameAdapter_typed k ht)
    | wrap h i o => exact .wrap (renameValue_typed h ht) (renameAdapter_typed i ht) (renameAdapter_typed o ht)
  theorem renameComp_typed (h : CompTyped env m a) (ht : RenamingTyped env target r) :
      CompTyped target (renameComp r m) a := by
    cases h with
    | ret h => exact .ret (renameValue_typed h ht)
    | force h => exact .force (renameValue_typed h ht)
    | chooseLeft h => exact .chooseLeft (renameValue_typed h ht)
    | chooseRight h => exact .chooseRight (renameValue_typed h ht)
    | absurd h => exact .absurd (renameValue_typed h ht)
    | bind h k => exact .bind (renameComp_typed h ht) (renameComp_typed k (up_typed ht _))
    | unionCase h l r =>
        exact .unionCase (renameValue_typed h ht)
          (renameComp_typed l (up_typed ht _)) (renameComp_typed r (up_typed ht _))
    | scope h => exact .scope (renameComp_typed h ht)
    | expose h => exact .expose (renameComp_typed h ht)
    | request h k => exact .request (renameValue_typed h ht) (renameComp_typed k (up_typed ht _))
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (renameValue_typed h ht) (renameValue_typed k ht)
  theorem renameAdapter_typed (h : AdapterTyped env adapter a b) (ht : RenamingTyped env target r) :
      AdapterTyped target (renameAdapter r adapter) a b := by
    cases h with
    | mk h => exact .mk (renameComp_typed h (up_typed ht _))
end

def SubstitutionTyped (env target : Context) (s : Nat → Value) : Prop :=
  ∀ i a, env i = some a → ValueTyped target (s i) a

theorem lift_typed (h : SubstitutionTyped env target s) (a : Ty) :
    SubstitutionTyped (extend env a) (extend target a) (lift s) := by
  intro i b hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst b
      exact .var rfl
  | succ i => exact renameValue_typed (h i b hi) (fun _ _ h => h)

mutual
  theorem substValue_typed (h : ValueTyped env v a) (ht : SubstitutionTyped env target s) :
      ValueTyped target (substValue s v) a := by
    cases h with
    | var h => exact ht _ _ h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (substComp_typed h ht)
    | inLeft h => exact .inLeft (substValue_typed h ht)
    | inRight h => exact .inRight (substValue_typed h ht)
    | top h => exact .top (substValue_typed h ht)
    | view h => exact .view (substValue_typed h ht)
    | both h k => exact .both (substValue_typed h ht) (substValue_typed k ht)
    | lambdaValue h k => exact .lambdaValue (substComp_typed h (lift_typed ht _)) (substAdapter_typed k ht)
    | lambdaComputation h k => exact .lambdaComputation (substComp_typed h (lift_typed ht _)) (substAdapter_typed k ht)
    | wrap h i o => exact .wrap (substValue_typed h ht) (substAdapter_typed i ht) (substAdapter_typed o ht)
  theorem substComp_typed (h : CompTyped env m a) (ht : SubstitutionTyped env target s) :
      CompTyped target (substComp s m) a := by
    cases h with
    | ret h => exact .ret (substValue_typed h ht)
    | force h => exact .force (substValue_typed h ht)
    | chooseLeft h => exact .chooseLeft (substValue_typed h ht)
    | chooseRight h => exact .chooseRight (substValue_typed h ht)
    | absurd h => exact .absurd (substValue_typed h ht)
    | bind h k => exact .bind (substComp_typed h ht) (substComp_typed k (lift_typed ht _))
    | unionCase h l r =>
        exact .unionCase (substValue_typed h ht)
          (substComp_typed l (lift_typed ht _)) (substComp_typed r (lift_typed ht _))
    | scope h => exact .scope (substComp_typed h ht)
    | expose h => exact .expose (substComp_typed h ht)
    | request h k => exact .request (substValue_typed h ht) (substComp_typed k (lift_typed ht _))
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (substValue_typed h ht) (substValue_typed k ht)
  theorem substAdapter_typed (h : AdapterTyped env adapter a b) (ht : SubstitutionTyped env target s) :
      AdapterTyped target (substAdapter s adapter) a b := by
    cases h with
    | mk h => exact .mk (substComp_typed h (lift_typed ht _))
end

def single (v : Value) : Nat → Value
  | 0 => v
  | n+1 => .var n

theorem substitute_top (hb : CompTyped (extend env a) body b) (hv : ValueTyped env v a) :
    CompTyped env (substComp (single v) body) b := by
  apply substComp_typed hb
  intro i t hi
  cases i with
  | zero =>
      simp only [extend, Option.some.injEq] at hi
      subst t
      exact hv
  | succ i => exact .var hi

/-- The result consumer belongs to the outer context; its own binder is lifted
by substAdapter exactly once. Types, receipt, paths and views are unchanged. -/
theorem substitute_lambda (s : Nat → Value) (mode receipt a b r body consumer) :
    substValue s (.lambda mode receipt a b r body consumer) =
      .lambda mode receipt a b r (substComp (lift s) body) (substAdapter s consumer) := rfl

theorem substitute_adapter (s : Nat → Value) (a b body paths views) :
    substAdapter s (.mk a b body paths views) =
      .mk a b (substComp (lift s) body) paths views := rfl

theorem substitute_request (s : Nat → Value) (op payload continuation) :
    substComp s (.request op payload continuation) =
      .request op (substValue s payload) (substComp (lift s) continuation) := rfl

end YulangClosure.HigherOrder
