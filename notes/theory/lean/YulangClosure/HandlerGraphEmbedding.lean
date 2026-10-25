import YulangClosure.HandlerGraphSyntax

namespace YulangClosure.HandlerGraph
open HigherOrder (Ty Context emptyContext extend OperationInstance ViewOccurrence ReceiptTemplate PathCorrespondence)
variable {R S : Type} {xi : R → Ty} {nu : S → Ty}

mutual
  def graphValue : HigherOrderGraph.Value R S → Value R S
    | .ref r => .ref r
    | .recvar s => .recvar s
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (graphComp m)
    | .inLeft v => .inLeft (graphValue v)
    | .inRight v => .inRight (graphValue v)
    | .both v => .both (graphValue v)
    | .top v => .top (graphValue v)
    | .view v o => .view (graphValue v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (graphComp body) (graphAdapter consumer)
    | .wrap f input output => .wrap (graphValue f) (graphAdapter input) (graphAdapter output)
  def graphComp : HigherOrderGraph.Comp R S → Comp R S
    | .ret v => .ret (graphValue v)
    | .force v => .force (graphValue v)
    | .chooseLeft v => .chooseLeft (graphValue v)
    | .chooseRight v => .chooseRight (graphValue v)
    | .absurd v => .absurd (graphValue v)
    | .bind m n => .bind (graphComp m) (graphComp n)
    | .unionCase v l right => .unionCase (graphValue v) (graphComp l) (graphComp right)
    | .scope owner body => .scope owner (graphComp body)
    | .expose ev rv body => .expose ev rv (graphComp body)
    | .request op v k => .request op (graphValue v) (graphComp k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (graphValue f) (graphValue a)
  def graphAdapter : HigherOrderGraph.Adapter R S → Adapter R S
    | .mk a b body paths views => .mk a b (graphComp body) paths views
end

mutual
  theorem graphValue_typed (h : HigherOrderGraph.ValueTyped xi nu env v a) :
      ValueTyped xi nu env (graphValue v) a := by
    cases h with
    | ref r => exact .ref r
    | recvar s => exact .recvar s
    | var h => exact .var h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (graphComp_typed h)
    | inLeft h => exact .inLeft (graphValue_typed h)
    | inRight h => exact .inRight (graphValue_typed h)
    | top h => exact .top (graphValue_typed h)
    | view h => exact .view (graphValue_typed h)
    | both h k => exact .both (graphValue_typed h) (graphValue_typed k)
    | lambdaValue h k => exact .lambdaValue (graphComp_typed h) (graphAdapter_typed k)
    | lambdaComputation h k => exact .lambdaComputation (graphComp_typed h) (graphAdapter_typed k)
    | wrap h i o => exact .wrap (graphValue_typed h) (graphAdapter_typed i) (graphAdapter_typed o)
  theorem graphComp_typed (h : HigherOrderGraph.CompTyped xi nu env m a) :
      CompTyped xi nu env (graphComp m) a := by
    cases h with
    | ret h => exact .ret (graphValue_typed h)
    | force h => exact .force (graphValue_typed h)
    | chooseLeft h => exact .chooseLeft (graphValue_typed h)
    | chooseRight h => exact .chooseRight (graphValue_typed h)
    | absurd h => exact .absurd (graphValue_typed h)
    | bind h k => exact .bind (graphComp_typed h) (graphComp_typed k)
    | unionCase h l r =>
        exact .unionCase (graphValue_typed h)
          (graphComp_typed l) (graphComp_typed r)
    | scope h => exact .scope (graphComp_typed h)
    | expose h => exact .expose (graphComp_typed h)
    | request h k => exact .request (graphValue_typed h) (graphComp_typed k)
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (graphValue_typed h) (graphValue_typed k)
  theorem graphAdapter_typed (h : HigherOrderGraph.AdapterTyped xi nu env adapter a b) :
      AdapterTyped xi nu env (graphAdapter adapter) a b := by
    cases h with
    | mk h => exact .mk (graphComp_typed h)
end

mutual
  def handlerValue : HigherOrder.Handler.Value → Value R S
    | .var i => .var i
    | .unit => .unit
    | .bool v => .bool v
    | .int v => .int v
    | .floatBits v => .floatBits v
    | .string v => .string v
    | .bytes v => .bytes v
    | .path v => .path v
    | .char v => .char v
    | .delay m => .delay (handlerComp m)
    | .inLeft v => .inLeft (handlerValue v)
    | .inRight v => .inRight (handlerValue v)
    | .both v => .both (handlerValue v)
    | .top v => .top (handlerValue v)
    | .view v o => .view (handlerValue v) o
    | .lambda mode receipt a b c body consumer =>
        .lambda mode receipt a b c (handlerComp body) (handlerAdapter consumer)
    | .wrap f input output => .wrap (handlerValue f) (handlerAdapter input) (handlerAdapter output)
  def handlerComp : HigherOrder.Handler.Comp → Comp R S
    | .ret v => .ret (handlerValue v)
    | .force v => .force (handlerValue v)
    | .chooseLeft v => .chooseLeft (handlerValue v)
    | .chooseRight v => .chooseRight (handlerValue v)
    | .absurd v => .absurd (handlerValue v)
    | .bind m n => .bind (handlerComp m) (handlerComp n)
    | .unionCase v l right => .unionCase (handlerValue v) (handlerComp l) (handlerComp right)
    | .scope owner body => .scope owner (handlerComp body)
    | .expose ev rv body => .expose ev rv (handlerComp body)
    | .request op v k => .request op (handlerValue v) (handlerComp k)
    | .fail reason => .fail reason
    | .dynamicCall f a => .dynamicCall (handlerValue f) (handlerValue a)
    | .handle h m => .handle (handlerHandler h) (handlerComp m)
    | .tryValue h v arms => .tryValue (handlerHandler h) (handlerValue v) (handlerValueArms arms)
    | .waitValue h v arms attempt => .waitValue (handlerHandler h) (handlerValue v)
        (handlerValueArms arms) (handlerComp attempt)
    | .tryOperation h op p k arms => .tryOperation (handlerHandler h) op (handlerValue p)
        (handlerComp k) (handlerOperationArms arms)
    | .waitOperation h op p k arms attempt => .waitOperation (handlerHandler h) op (handlerValue p)
        (handlerComp k) (handlerOperationArms arms) (handlerComp attempt)
  def handlerHandler : HigherOrder.Handler.Handler → Handler R S
    | .mk id a b vs os => .mk id a b (handlerValueArms vs) (handlerOperationArms os)
  def handlerValueArms : HigherOrder.Handler.ValueArms → ValueArms R S
    | .nil => .nil
    | .cons body rest => .cons (handlerComp body) (handlerValueArms rest)
  def handlerOperationArms : HigherOrder.Handler.OperationArms → OperationArms R S
    | .nil => .nil
    | .cons op eligible body rest => .cons op eligible (handlerComp body)
        (handlerOperationArms rest)
  def handlerAdapter : HigherOrder.Handler.Adapter → Adapter R S
    | .mk a b body paths views => .mk a b (handlerComp body) paths views
end

mutual
  theorem handlerValue_typed (h : HigherOrder.Handler.ValueTyped env v a) :
      ValueTyped xi nu env (handlerValue v) a := by
    cases h with
    | var h => exact .var h
    | unit => exact .unit
    | bool => exact .bool
    | int => exact .int
    | floatBits => exact .floatBits
    | string => exact .string
    | bytes => exact .bytes
    | path => exact .path
    | char => exact .char
    | delay h => exact .delay (handlerComp_typed h)
    | inLeft h => exact .inLeft (handlerValue_typed h)
    | inRight h => exact .inRight (handlerValue_typed h)
    | top h => exact .top (handlerValue_typed h)
    | view h => exact .view (handlerValue_typed h)
    | both h k => exact .both (handlerValue_typed h) (handlerValue_typed k)
    | lambdaValue h k => exact .lambdaValue (handlerComp_typed h ) (handlerAdapter_typed k)
    | lambdaComputation h k => exact .lambdaComputation (handlerComp_typed h ) (handlerAdapter_typed k)
    | wrap h i o => exact .wrap (handlerValue_typed h) (handlerAdapter_typed i) (handlerAdapter_typed o)
  theorem handlerComp_typed (h : HigherOrder.Handler.CompTyped env m a) :
      CompTyped xi nu env (handlerComp m) a := by
    cases h with
    | ret h => exact .ret (handlerValue_typed h)
    | force h => exact .force (handlerValue_typed h)
    | chooseLeft h => exact .chooseLeft (handlerValue_typed h)
    | chooseRight h => exact .chooseRight (handlerValue_typed h)
    | absurd h => exact .absurd (handlerValue_typed h)
    | bind h k => exact .bind (handlerComp_typed h) (handlerComp_typed k )
    | unionCase h l r =>
        exact .unionCase (handlerValue_typed h)
          (handlerComp_typed l ) (handlerComp_typed r )
    | scope h => exact .scope (handlerComp_typed h)
    | expose h => exact .expose (handlerComp_typed h)
    | request h k => exact .request (handlerValue_typed h) (handlerComp_typed k )
    | fail => exact .fail
    | dynamicCall h k => exact .dynamicCall (handlerValue_typed h) (handlerValue_typed k)
    | handle hh hm => exact .handle (handlerHandler_typed hh) (handlerComp_typed hm)
    | tryValue hh hv hs => exact .tryValue (handlerHandler_typed hh) (handlerValue_typed hv) (handlerValueArms_typed hs)
    | waitValue hh hv hs hm => exact .waitValue (handlerHandler_typed hh) (handlerValue_typed hv) (handlerValueArms_typed hs) (handlerComp_typed hm)
    | tryOperation hh hp hk hs => exact .tryOperation (handlerHandler_typed hh) (handlerValue_typed hp) (handlerComp_typed hk ) (handlerOperationArms_typed hs)
    | waitOperation hh hp hk hs hm => exact .waitOperation (handlerHandler_typed hh) (handlerValue_typed hp) (handlerComp_typed hk ) (handlerOperationArms_typed hs) (handlerComp_typed hm)
  theorem handlerHandler_typed (h : HigherOrder.Handler.HandlerTyped env handler a b) :
      HandlerTyped xi nu env (handlerHandler handler) a b := by
    cases h with
    | mk hv ho => exact .mk (handlerValueArms_typed hv) (handlerOperationArms_typed ho)
  theorem handlerValueArms_typed (h : HigherOrder.Handler.ValueArmsTyped env arms a b) :
      ValueArmsTyped xi nu env (handlerValueArms arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (handlerComp_typed hb ) (handlerValueArms_typed hr)
  theorem handlerOperationArms_typed (h : HigherOrder.Handler.OperationArmsTyped env arms a b) :
      OperationArmsTyped xi nu env (handlerOperationArms arms) a b := by
    cases h with
    | nil => exact .nil
    | cons hb hr => exact .cons (handlerComp_typed hb ) (handlerOperationArms_typed hr)
  theorem handlerAdapter_typed (h : HigherOrder.Handler.AdapterTyped env adapter a b) :
      AdapterTyped xi nu env (handlerAdapter adapter) a b := by
    cases h with
    | mk h => exact .mk (handlerComp_typed h )
end


abbrev Graph (R : Type) := R → Value R Empty

def WellTyped (graph : Graph R) (xi : R → Ty) : Prop :=
  ∀ r, ValueTyped xi emptyTy emptyContext (graph r) (xi r)

/-- Only genuine data introductions, lambda and delay stop transparent
inspection. Intersection/top evidence, views, and callable adapter wrappers
do not turn an alias cycle into a constructed value. Local variables cannot
occur at the head of a well-typed closed graph node. -/
def frontier : Value R S → Option (Sum R S)
  | .ref r => some (.inl r)
  | .recvar s => some (.inr s)
  | .both v | .top v | .view v _ | .wrap v _ _ => frontier v
  | _ => none

def nextValue (v : Value R Empty) : Option R :=
  (frontier v).map (Sum.elim id Empty.elim)

/-- Unit is ONLY a terminal token in the untyped guard projection. It is
never the encoding, type, or canonical form of the higher-order value. -/
def projectNode (v : Value R Empty) : GuardedValueGraph.Node R :=
  match nextValue v with
  | none => .unit
  | some r => .alias r

def projectGraph (graph : Graph R) : GuardedValueGraph.Graph R :=
  fun r => projectNode (graph r)

theorem projectNode_next (v : Value R Empty) :
    (projectNode v).next = nextValue v := by
  unfold projectNode
  cases nextValue v <;> rfl

theorem projection_edge (graph : Graph R) (r s : R) :
    (projectGraph graph r).next = some s ↔ nextValue (graph r) = some s := by
  rw [projectGraph, projectNode_next]


def liftGraph (g : HigherOrderGraph.Graph R) : Graph R := fun r => graphValue (g r)

theorem liftGraph_typed (h : HigherOrderGraph.WellTyped g xi) : WellTyped (liftGraph g) xi :=
  fun r => graphValue_typed (h r)

theorem graph_frontier (v : HigherOrderGraph.Value R S) :
    frontier (graphValue v) = HigherOrderGraph.frontier v := by
  cases v with
  | both v => exact graph_frontier v
  | top v => exact graph_frontier v
  | view v o => exact graph_frontier v
  | wrap v i o => exact graph_frontier v
  | ref r => rfl
  | recvar s => rfl
  | var i => rfl
  | unit => rfl
  | bool v => rfl
  | int v => rfl
  | floatBits v => rfl
  | string v => rfl
  | bytes v => rfl
  | path v => rfl
  | char v => rfl
  | delay m => rfl
  | inLeft v => rfl
  | inRight v => rfl
  | lambda mode receipt a b c body consumer => rfl

theorem graph_next (v : HigherOrderGraph.Value R Empty) :
    nextValue (graphValue v) = HigherOrderGraph.nextValue v := by
  unfold nextValue HigherOrderGraph.nextValue
  rw [graph_frontier]

theorem liftGraph_projection (g : HigherOrderGraph.Graph R) :
    projectGraph (liftGraph g) = HigherOrderGraph.projectGraph g := by
  funext r
  simp only [projectGraph, liftGraph, projectNode, graph_next,
    HigherOrderGraph.projectGraph, HigherOrderGraph.projectNode]
  rfl

def liftGraph_guard (g : HigherOrderGraph.Graph R)
    (h : GuardedValueGraph.Guarded (HigherOrderGraph.projectGraph g)) :
    GuardedValueGraph.Guarded (projectGraph (liftGraph g)) :=
  (liftGraph_projection g).symm ▸ h


mutual
  theorem graphValue_rename (r : Nat → Nat) (v : HigherOrderGraph.Value R S) :
      graphValue (HigherOrderGraph.renameValue r v) = renameValue r (graphValue (R := R) (S := S) v) := by
    cases v with
    | ref r => rfl
    | recvar s => rfl
    | var i => rfl
    | unit  => rfl
    | bool v => rfl
    | int v => rfl
    | floatBits v => rfl
    | string v => rfl
    | bytes v => rfl
    | path v => rfl
    | char v => rfl
    | delay m => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphComp_rename r m]
    | inLeft v => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphValue_rename r v]
    | inRight v => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphValue_rename r v]
    | both v => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphValue_rename r v]
    | top v => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphValue_rename r v]
    | view v o => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphValue_rename r v]
    | lambda mode receipt a b c body consumer => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphComp_rename (Original.up r) body, graphAdapter_rename r consumer]
    | wrap f input output => 
        simp only [HigherOrderGraph.renameValue, graphValue, renameValue]
        rw [graphValue_rename r f, graphAdapter_rename r input, graphAdapter_rename r output]
  theorem graphComp_rename (r : Nat → Nat) (v : HigherOrderGraph.Comp R S) :
      graphComp (HigherOrderGraph.renameComp r v) = renameComp r (graphComp (R := R) (S := S) v) := by
    cases v with
    | ret v => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r v]
    | force v => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r v]
    | chooseLeft v => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r v]
    | chooseRight v => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r v]
    | absurd v => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r v]
    | bind m n => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphComp_rename r m, graphComp_rename (Original.up r) n]
    | unionCase v l right => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r v, graphComp_rename (Original.up r) l, graphComp_rename (Original.up r) right]
    | scope owner body => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphComp_rename r body]
    | expose ev rv body => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphComp_rename r body]
    | request op v k => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r v, graphComp_rename (Original.up r) k]
    | fail reason => rfl
    | dynamicCall f a => 
        simp only [HigherOrderGraph.renameComp, graphComp, renameComp]
        rw [graphValue_rename r f, graphValue_rename r a]
  theorem graphAdapter_rename (r : Nat → Nat) (v : HigherOrderGraph.Adapter R S) :
      graphAdapter (HigherOrderGraph.renameAdapter r v) = renameAdapter r (graphAdapter (R := R) (S := S) v) := by
    cases v with
    | mk a b body paths views => 
        simp only [HigherOrderGraph.renameAdapter, graphAdapter, renameAdapter]
        rw [graphComp_rename (Original.up r) body]
end

theorem graph_lift_compat {s : Nat → HigherOrderGraph.Value R S} {t : Nat → Value R S}
    (hs : ∀ i, graphValue (s i) = t i) :
    ∀ i, graphValue (HigherOrderGraph.lift s i) = lift t i := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [HigherOrderGraph.lift, lift, graphValue_rename, hs]

mutual
  theorem graphValue_subst (v : HigherOrderGraph.Value R S) (s : Nat → HigherOrderGraph.Value R S) (t : Nat → Value R S)
      (hs : ∀ i, graphValue (s i) = t i) :
      graphValue (HigherOrderGraph.substValue s v) = substValue t (graphValue v) := by
    cases v with
    | ref r => rfl
    | recvar s => rfl
    | var i => exact hs i
    | unit  => rfl
    | bool v => rfl
    | int v => rfl
    | floatBits v => rfl
    | string v => rfl
    | bytes v => rfl
    | path v => rfl
    | char v => rfl
    | delay m => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphComp_subst m s t hs]
    | inLeft v => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphValue_subst v s t hs]
    | inRight v => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphValue_subst v s t hs]
    | both v => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphValue_subst v s t hs]
    | top v => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphValue_subst v s t hs]
    | view v o => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphValue_subst v s t hs]
    | lambda mode receipt a b c body consumer => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphComp_subst body (HigherOrderGraph.lift s) (lift t) (graph_lift_compat hs), graphAdapter_subst consumer s t hs]
    | wrap f input output => 
        simp only [HigherOrderGraph.substValue, graphValue, substValue]
        rw [graphValue_subst f s t hs, graphAdapter_subst input s t hs, graphAdapter_subst output s t hs]
  theorem graphComp_subst (v : HigherOrderGraph.Comp R S) (s : Nat → HigherOrderGraph.Value R S) (t : Nat → Value R S)
      (hs : ∀ i, graphValue (s i) = t i) :
      graphComp (HigherOrderGraph.substComp s v) = substComp t (graphComp v) := by
    cases v with
    | ret v => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst v s t hs]
    | force v => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst v s t hs]
    | chooseLeft v => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst v s t hs]
    | chooseRight v => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst v s t hs]
    | absurd v => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst v s t hs]
    | bind m n => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphComp_subst m s t hs, graphComp_subst n (HigherOrderGraph.lift s) (lift t) (graph_lift_compat hs)]
    | unionCase v l right => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst v s t hs, graphComp_subst l (HigherOrderGraph.lift s) (lift t) (graph_lift_compat hs), graphComp_subst right (HigherOrderGraph.lift s) (lift t) (graph_lift_compat hs)]
    | scope owner body => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphComp_subst body s t hs]
    | expose ev rv body => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphComp_subst body s t hs]
    | request op v k => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst v s t hs, graphComp_subst k (HigherOrderGraph.lift s) (lift t) (graph_lift_compat hs)]
    | fail reason => rfl
    | dynamicCall f a => 
        simp only [HigherOrderGraph.substComp, graphComp, substComp]
        rw [graphValue_subst f s t hs, graphValue_subst a s t hs]
  theorem graphAdapter_subst (v : HigherOrderGraph.Adapter R S) (s : Nat → HigherOrderGraph.Value R S) (t : Nat → Value R S)
      (hs : ∀ i, graphValue (s i) = t i) :
      graphAdapter (HigherOrderGraph.substAdapter s v) = substAdapter t (graphAdapter v) := by
    cases v with
    | mk a b body paths views => 
        simp only [HigherOrderGraph.substAdapter, graphAdapter, substAdapter]
        rw [graphComp_subst body (HigherOrderGraph.lift s) (lift t) (graph_lift_compat hs)]
end

mutual
  theorem handlerValue_rename (r : Nat → Nat) (v : HigherOrder.Handler.Value) :
      handlerValue (HigherOrder.Handler.renameValue r v) = renameValue r (handlerValue (R := R) (S := S) v) := by
    cases v with
    | var i => rfl
    | unit  => rfl
    | bool v => rfl
    | int v => rfl
    | floatBits v => rfl
    | string v => rfl
    | bytes v => rfl
    | path v => rfl
    | char v => rfl
    | delay m => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerComp_rename r m]
    | inLeft v => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerValue_rename r v]
    | inRight v => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerValue_rename r v]
    | both v => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerValue_rename r v]
    | top v => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerValue_rename r v]
    | view v o => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerValue_rename r v]
    | lambda mode receipt a b c body consumer => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerComp_rename (Original.up r) body, handlerAdapter_rename r consumer]
    | wrap f input output => 
        simp only [HigherOrder.Handler.renameValue, handlerValue, renameValue]
        rw [handlerValue_rename r f, handlerAdapter_rename r input, handlerAdapter_rename r output]
  theorem handlerComp_rename (r : Nat → Nat) (v : HigherOrder.Handler.Comp) :
      handlerComp (HigherOrder.Handler.renameComp r v) = renameComp r (handlerComp (R := R) (S := S) v) := by
    cases v with
    | ret v => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r v]
    | force v => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r v]
    | chooseLeft v => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r v]
    | chooseRight v => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r v]
    | absurd v => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r v]
    | bind m n => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerComp_rename r m, handlerComp_rename (Original.up r) n]
    | unionCase v l right => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r v, handlerComp_rename (Original.up r) l, handlerComp_rename (Original.up r) right]
    | scope owner body => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerComp_rename r body]
    | expose ev rv body => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerComp_rename r body]
    | request op v k => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r v, handlerComp_rename (Original.up r) k]
    | fail reason => rfl
    | dynamicCall f a => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerValue_rename r f, handlerValue_rename r a]
    | handle h m => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerHandler_rename r h, handlerComp_rename r m]
    | tryValue h v arms => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerHandler_rename r h, handlerValue_rename r v, handlerValueArms_rename r arms]
    | waitValue h v arms attempt => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerHandler_rename r h, handlerValue_rename r v, handlerValueArms_rename r arms, handlerComp_rename r attempt]
    | tryOperation h op p k arms => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerHandler_rename r h, handlerValue_rename r p, handlerComp_rename (Original.up r) k, handlerOperationArms_rename r arms]
    | waitOperation h op p k arms attempt => 
        simp only [HigherOrder.Handler.renameComp, handlerComp, renameComp]
        rw [handlerHandler_rename r h, handlerValue_rename r p, handlerComp_rename (Original.up r) k, handlerOperationArms_rename r arms, handlerComp_rename r attempt]
  theorem handlerHandler_rename (r : Nat → Nat) (v : HigherOrder.Handler.Handler) :
      handlerHandler (HigherOrder.Handler.renameHandler r v) = renameHandler r (handlerHandler (R := R) (S := S) v) := by
    cases v with
    | mk id a b vs os => 
        simp only [HigherOrder.Handler.renameHandler, handlerHandler, renameHandler]
        rw [handlerValueArms_rename r vs, handlerOperationArms_rename r os]
  theorem handlerValueArms_rename (r : Nat → Nat) (v : HigherOrder.Handler.ValueArms) :
      handlerValueArms (HigherOrder.Handler.renameValueArms r v) = renameValueArms r (handlerValueArms (R := R) (S := S) v) := by
    cases v with
    | nil  => rfl
    | cons body rest => 
        simp only [HigherOrder.Handler.renameValueArms, handlerValueArms, renameValueArms]
        rw [handlerComp_rename (Original.up r) body, handlerValueArms_rename r rest]
  theorem handlerOperationArms_rename (r : Nat → Nat) (v : HigherOrder.Handler.OperationArms) :
      handlerOperationArms (HigherOrder.Handler.renameOperationArms r v) = renameOperationArms r (handlerOperationArms (R := R) (S := S) v) := by
    cases v with
    | nil  => rfl
    | cons op eligible body rest => 
        simp only [HigherOrder.Handler.renameOperationArms, handlerOperationArms, renameOperationArms]
        rw [handlerComp_rename (Original.up (Original.up r)) body, handlerOperationArms_rename r rest]
  theorem handlerAdapter_rename (r : Nat → Nat) (v : HigherOrder.Handler.Adapter) :
      handlerAdapter (HigherOrder.Handler.renameAdapter r v) = renameAdapter r (handlerAdapter (R := R) (S := S) v) := by
    cases v with
    | mk a b body paths views => 
        simp only [HigherOrder.Handler.renameAdapter, handlerAdapter, renameAdapter]
        rw [handlerComp_rename (Original.up r) body]
end

theorem handler_lift_compat {s : Nat → HigherOrder.Handler.Value} {t : Nat → Value R S}
    (hs : ∀ i, handlerValue (s i) = t i) :
    ∀ i, handlerValue (HigherOrder.Handler.lift s i) = lift t i := by
  intro i
  cases i with
  | zero => rfl
  | succ i =>
      simp only [HigherOrder.Handler.lift, lift, handlerValue_rename, hs]

mutual
  theorem handlerValue_subst (v : HigherOrder.Handler.Value) (s : Nat → HigherOrder.Handler.Value) (t : Nat → Value R S)
      (hs : ∀ i, handlerValue (s i) = t i) :
      handlerValue (HigherOrder.Handler.substValue s v) = substValue t (handlerValue v) := by
    cases v with
    | var i => exact hs i
    | unit  => rfl
    | bool v => rfl
    | int v => rfl
    | floatBits v => rfl
    | string v => rfl
    | bytes v => rfl
    | path v => rfl
    | char v => rfl
    | delay m => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerComp_subst m s t hs]
    | inLeft v => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerValue_subst v s t hs]
    | inRight v => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerValue_subst v s t hs]
    | both v => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerValue_subst v s t hs]
    | top v => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerValue_subst v s t hs]
    | view v o => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerValue_subst v s t hs]
    | lambda mode receipt a b c body consumer => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerComp_subst body (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs), handlerAdapter_subst consumer s t hs]
    | wrap f input output => 
        simp only [HigherOrder.Handler.substValue, handlerValue, substValue]
        rw [handlerValue_subst f s t hs, handlerAdapter_subst input s t hs, handlerAdapter_subst output s t hs]
  theorem handlerComp_subst (v : HigherOrder.Handler.Comp) (s : Nat → HigherOrder.Handler.Value) (t : Nat → Value R S)
      (hs : ∀ i, handlerValue (s i) = t i) :
      handlerComp (HigherOrder.Handler.substComp s v) = substComp t (handlerComp v) := by
    cases v with
    | ret v => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst v s t hs]
    | force v => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst v s t hs]
    | chooseLeft v => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst v s t hs]
    | chooseRight v => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst v s t hs]
    | absurd v => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst v s t hs]
    | bind m n => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerComp_subst m s t hs, handlerComp_subst n (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs)]
    | unionCase v l right => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst v s t hs, handlerComp_subst l (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs), handlerComp_subst right (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs)]
    | scope owner body => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerComp_subst body s t hs]
    | expose ev rv body => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerComp_subst body s t hs]
    | request op v k => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst v s t hs, handlerComp_subst k (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs)]
    | fail reason => rfl
    | dynamicCall f a => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerValue_subst f s t hs, handlerValue_subst a s t hs]
    | handle h m => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerHandler_subst h s t hs, handlerComp_subst m s t hs]
    | tryValue h v arms => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerHandler_subst h s t hs, handlerValue_subst v s t hs, handlerValueArms_subst arms s t hs]
    | waitValue h v arms attempt => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerHandler_subst h s t hs, handlerValue_subst v s t hs, handlerValueArms_subst arms s t hs, handlerComp_subst attempt s t hs]
    | tryOperation h op p k arms => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerHandler_subst h s t hs, handlerValue_subst p s t hs, handlerComp_subst k (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs), handlerOperationArms_subst arms s t hs]
    | waitOperation h op p k arms attempt => 
        simp only [HigherOrder.Handler.substComp, handlerComp, substComp]
        rw [handlerHandler_subst h s t hs, handlerValue_subst p s t hs, handlerComp_subst k (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs), handlerOperationArms_subst arms s t hs, handlerComp_subst attempt s t hs]
  theorem handlerHandler_subst (v : HigherOrder.Handler.Handler) (s : Nat → HigherOrder.Handler.Value) (t : Nat → Value R S)
      (hs : ∀ i, handlerValue (s i) = t i) :
      handlerHandler (HigherOrder.Handler.substHandler s v) = substHandler t (handlerHandler v) := by
    cases v with
    | mk id a b vs os => 
        simp only [HigherOrder.Handler.substHandler, handlerHandler, substHandler]
        rw [handlerValueArms_subst vs s t hs, handlerOperationArms_subst os s t hs]
  theorem handlerValueArms_subst (v : HigherOrder.Handler.ValueArms) (s : Nat → HigherOrder.Handler.Value) (t : Nat → Value R S)
      (hs : ∀ i, handlerValue (s i) = t i) :
      handlerValueArms (HigherOrder.Handler.substValueArms s v) = substValueArms t (handlerValueArms v) := by
    cases v with
    | nil  => rfl
    | cons body rest => 
        simp only [HigherOrder.Handler.substValueArms, handlerValueArms, substValueArms]
        rw [handlerComp_subst body (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs), handlerValueArms_subst rest s t hs]
  theorem handlerOperationArms_subst (v : HigherOrder.Handler.OperationArms) (s : Nat → HigherOrder.Handler.Value) (t : Nat → Value R S)
      (hs : ∀ i, handlerValue (s i) = t i) :
      handlerOperationArms (HigherOrder.Handler.substOperationArms s v) = substOperationArms t (handlerOperationArms v) := by
    cases v with
    | nil  => rfl
    | cons op eligible body rest => 
        simp only [HigherOrder.Handler.substOperationArms, handlerOperationArms, substOperationArms]
        rw [handlerComp_subst body (HigherOrder.Handler.lift (HigherOrder.Handler.lift s)) (lift (lift t)) (handler_lift_compat (handler_lift_compat hs)), handlerOperationArms_subst rest s t hs]
  theorem handlerAdapter_subst (v : HigherOrder.Handler.Adapter) (s : Nat → HigherOrder.Handler.Value) (t : Nat → Value R S)
      (hs : ∀ i, handlerValue (s i) = t i) :
      handlerAdapter (HigherOrder.Handler.substAdapter s v) = substAdapter t (handlerAdapter v) := by
    cases v with
    | mk a b body paths views => 
        simp only [HigherOrder.Handler.substAdapter, handlerAdapter, substAdapter]
        rw [handlerComp_subst body (HigherOrder.Handler.lift s) (lift t) (handler_lift_compat hs)]
end

end YulangClosure.HandlerGraph
