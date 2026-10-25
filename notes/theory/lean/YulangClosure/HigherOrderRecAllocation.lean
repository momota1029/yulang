import YulangClosure.HigherOrderGraphSyntax
import YulangClosure.FiniteGuardDecision

/-! Source recursive RHS allocation for the full accepted higher-order grammar.
The transparent projection is a guard certificate, never a value-typing oracle. -/
namespace YulangClosure.HigherOrderGraph
open HigherOrder (Ty Context emptyContext extend ReceiptTemplate OperationInstance)

variable {R S T : Type}

def joinTy (xi : R → Ty) (nu : S → Ty) : Sum R S → Ty
  | .inl r => xi r
  | .inr s => nu s

/-- Source convention: all n recursive names occupy the nearest prefix;
outer context index i occupies index n+i. Ordinary binders extend this context
one slot at a time. This is a concrete representation of Γ,x̄:Ā. -/
def sourceContext (nu : Fin n → Ty) (env : Context) : Context := fun i =>
  if h : i < n then some (nu ⟨i, h⟩) else env (i - n)

def splitNames (n : Nat) : Nat → Value R (Fin n) := fun i =>
  if h : i < n then .recvar ⟨i, h⟩ else .var (i - n)

theorem splitNames_typed {xi : R → Ty} {nu : Fin n → Ty} :
    SubstitutionTyped xi nu (sourceContext nu env) env (splitNames n) := by
  intro i a hi
  by_cases h : i < n
  · simp only [sourceContext, dite_eq_left h, Option.some.injEq] at hi
    subst a
    simpa only [splitNames, dite_eq_left h] using
      (ValueTyped.recvar (xi := xi) (nu := nu) (env := env) ⟨i, h⟩)
  · simp only [sourceContext, dite_eq_right h] at hi
    simpa only [splitNames, dite_eq_right h] using (ValueTyped.var (xi := xi) (nu := nu) hi)

def splitValue (n : Nat) (v : HigherOrder.Value) : Value R (Fin n) :=
  substValue (splitNames n) (embedValue v)

def splitComp (n : Nat) (m : HigherOrder.Comp) : Comp R (Fin n) :=
  substComp (splitNames n) (embedComp m)

def splitAdapter (n : Nat) (adapter : HigherOrder.Adapter) : Adapter R (Fin n) :=
  substAdapter (splitNames n) (embedAdapter adapter)

theorem splitValue_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : HigherOrder.ValueTyped (sourceContext nu env) v a) :
    ValueTyped xi nu env (splitValue n v) a :=
  substValue_typed (embedValue_typed h) splitNames_typed

theorem splitComp_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : HigherOrder.CompTyped (sourceContext nu env) m a) :
    CompTyped xi nu env (splitComp n m) a :=
  substComp_typed (embedComp_typed h) splitNames_typed

theorem splitAdapter_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : HigherOrder.AdapterTyped (sourceContext nu env) adapter a b) :
    AdapterTyped xi nu env (splitAdapter n adapter) a b :=
  substAdapter_typed (embedAdapter_typed h) splitNames_typed

theorem source_recursive_lookup (nu : Fin n → Ty) (env : Context) (s : Fin n) :
    sourceContext nu env s.val = some (nu s) := by
  simp [sourceContext, s.isLt]

theorem source_outer_lookup (nu : Fin n → Ty) (env : Context) (i : Nat) :
    sourceContext nu env (n + i) = env i := by
  simp [sourceContext, Nat.not_lt.mpr (Nat.le_add_right n i)]

theorem split_recursive (s : Fin n) :
    splitNames (R := R) n s.val = .recvar s := by
  simp [splitNames, s.isLt]

theorem split_outer (i : Nat) :
    splitNames (R := R) n (n + i) = .var i := by
  simp [splitNames, Nat.not_lt.mpr (Nat.le_add_right n i)]

/-- The newly bound argument/response/input remains local index zero. -/
theorem split_bound_zero :
    lift (splitNames (R := R) n) 0 = .var 0 := rfl

theorem split_bound_recursive (s : Fin n) :
    lift (splitNames (R := R) n) (s.val + 1) = .recvar s := by
  simp [lift, split_recursive, renameValue]

/-- Closed old values can be captured independently of every fresh node. -/
def CapturesTyped (xi : R → Ty) (env : Context) (capture : Nat → Value R Empty) : Prop :=
  ∀ i a, env i = some a → ValueTyped xi emptyTy emptyContext (capture i) a

def mapOld (f : R → T) (v : Value R Empty) : Value T Empty :=
  closeNamesValue f Empty.elim v

theorem mapOld_typed {xi : R → Ty} {tau : T → Ty}
    (f : R → T) (hf : ∀ r, tau (f r) = xi r)
    (h : ValueTyped xi emptyTy env v a) :
    ValueTyped tau emptyTy env (mapOld f v) a :=
  closeNamesValue_typed h f Empty.elim hf (fun e => Empty.elim e)

def closedCapture (capture : Nat → Value R Empty) : Nat → Value (Sum R S) Empty :=
  fun i => mapOld Sum.inl (capture i)

/-- Recursive names are closed simultaneously, then the independently typed
outer environment is substituted. No new node is used to type the captures. -/
def closeValue (capture : Nat → Value R Empty) (v : Value R S) :
    Value (Sum R S) Empty :=
  substValue (closedCapture capture) (closeNamesValue Sum.inl Sum.inr v)

def closeComp (capture : Nat → Value R Empty) (m : Comp R S) :
    Comp (Sum R S) Empty :=
  substComp (closedCapture capture) (closeNamesComp Sum.inl Sum.inr m)

def closeAdapter (capture : Nat → Value R Empty) (adapter : Adapter R S) :
    Adapter (Sum R S) Empty :=
  substAdapter (closedCapture capture) (closeNamesAdapter Sum.inl Sum.inr adapter)

theorem closedCapture_typed {xi : R → Ty} {nu : S → Ty}
    (hc : CapturesTyped xi env capture) :
    SubstitutionTyped (joinTy xi nu) emptyTy env emptyContext (closedCapture capture) := by
  intro i a hi
  exact mapOld_typed Sum.inl (fun _ => rfl) (hc i a hi)

theorem closeValue_typed {xi : R → Ty} {nu : S → Ty}
    (h : ValueTyped xi nu env v a) (hc : CapturesTyped xi env capture) :
    ValueTyped (joinTy xi nu) emptyTy emptyContext (closeValue capture v) a :=
  substValue_typed
    (closeNamesValue_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

theorem closeComp_typed {xi : R → Ty} {nu : S → Ty}
    (h : CompTyped xi nu env m a) (hc : CapturesTyped xi env capture) :
    CompTyped (joinTy xi nu) emptyTy emptyContext (closeComp capture m) a :=
  substComp_typed
    (closeNamesComp_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

theorem closeAdapter_typed {xi : R → Ty} {nu : S → Ty}
    (h : AdapterTyped xi nu env adapter a b) (hc : CapturesTyped xi env capture) :
    AdapterTyped (joinTy xi nu) emptyTy emptyContext (closeAdapter capture adapter) a b :=
  substAdapter_typed
    (closeNamesAdapter_typed h Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl))
    (closedCapture_typed hc)

def sourceCloseValue (capture : Nat → Value R Empty) (n : Nat)
    (v : HigherOrder.Value) : Value (Sum R (Fin n)) Empty :=
  closeValue capture (splitValue n v)

def sourceCloseComp (capture : Nat → Value R Empty) (n : Nat)
    (m : HigherOrder.Comp) : Comp (Sum R (Fin n)) Empty :=
  closeComp capture (splitComp n m)

theorem sourceCloseValue_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : HigherOrder.ValueTyped (sourceContext nu env) v a)
    (hc : CapturesTyped xi env capture) :
    ValueTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseValue capture n v) a :=
  closeValue_typed (splitValue_typed h) hc

theorem sourceCloseComp_typed {xi : R → Ty} {nu : Fin n → Ty}
    (h : HigherOrder.CompTyped (sourceContext nu env) m a)
    (hc : CapturesTyped xi env capture) :
    CompTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseComp capture n m) a :=
  closeComp_typed (splitComp_typed h) hc

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

/-- Exact equation from the actual recursive-name constructor to the target
reference, including arbitrarily nested transparent wrappers. -/
theorem frontier_closeNames (f : R → T) (g : S → T) (v : Value R S) :
    nextValue (closeNamesValue f g v) =
      (frontier v).map (Sum.elim f g) := by
  cases v with
  | ref r => rfl
  | recvar s => rfl
  | both v => exact frontier_closeNames f g v
  | top v => exact frontier_closeNames f g v
  | view v o => exact frontier_closeNames f g v
  | wrap v i o => exact frontier_closeNames f g v
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

theorem next_mapOld (f : R → T) (v : Value R Empty) :
    nextValue (mapOld f v) = (nextValue v).map f := by
  rw [mapOld, frontier_closeNames]
  unfold nextValue
  cases h : frontier v with
  | none => rfl
  | some r =>
      cases r with
      | inl r => rfl
      | inr e => exact Empty.elim e

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

theorem projectNode_map (f : R → T) (v : Value R Empty) :
    projectNode (mapOld f v) = (projectNode v).map f := by
  unfold projectNode
  rw [next_mapOld]
  cases nextValue v <;> rfl

def allocate (graph : Graph R) (fresh : S → Value (Sum R S) Empty) : Graph (Sum R S)
  | .inl r => mapOld Sum.inl (graph r)
  | .inr s => fresh s

theorem allocation_old_node (graph : Graph R) (fresh : S → Value (Sum R S) Empty) (r : R) :
    allocate graph fresh (.inl r) = mapOld Sum.inl (graph r) := rfl

theorem allocation_old_type (xi : R → Ty) (nu : S → Ty) (r : R) :
    joinTy xi nu (.inl r) = xi r := rfl

theorem fresh_no_collision (r : R) (s : S) :
    (Sum.inl r : Sum R S) ≠ Sum.inr s := by intro h; cases h

theorem fresh_names_distinct {s t : S} (hne : s ≠ t) :
    (Sum.inr s : Sum R S) ≠ Sum.inr t := by
  intro h
  exact hne (Sum.inr.inj h)

theorem old_no_fresh_edge (graph : Graph R) (fresh : S → Value (Sum R S) Empty)
    (r : R) (s : S) :
    nextValue (allocate graph fresh (.inl r)) ≠ some (.inr s) := by
  change nextValue (mapOld Sum.inl (graph r)) ≠ _
  rw [next_mapOld]
  cases nextValue (graph r) <;> simp

theorem allocate_typed {graph : Graph R} {xi : R → Ty} {nu : S → Ty}
    (hg : WellTyped graph xi) (fresh : S → Value (Sum R S) Empty)
    (hf : ∀ s, ValueTyped (joinTy xi nu) emptyTy emptyContext (fresh s) (nu s)) :
    WellTyped (allocate graph fresh) (joinTy xi nu) := by
  intro r
  cases r with
  | inl r => exact mapOld_typed Sum.inl (fun _ => rfl) (hg r)
  | inr s => exact hf s

/-- Projection commutes with the actual immutable allocation constructor. -/
theorem project_allocation (graph : Graph R) (fresh : S → Value (Sum R S) Empty) :
    projectGraph (allocate graph fresh) =
      GuardedValueGraph.allocate (projectGraph graph) (fun s => projectNode (fresh s)) := by
  funext r
  cases r with
  | inl r => exact projectNode_map Sum.inl (graph r)
  | inr s => rfl

def FreshNoCycle (fresh : Fin n → Value (Sum R (Fin n)) Empty) : Prop :=
  GuardedValueGraph.FiniteDecision.FreshNoCycle (fun s => projectNode (fresh s))

theorem fresh_edge (fresh : Fin n → Value (Sum R (Fin n)) Empty) (s t : Fin n) :
    (GuardedValueGraph.FiniteDecision.freshGraph (fun i => projectNode (fresh i)) s).next = some t ↔
      nextValue (fresh s) = some (.inr t) := by
  rw [GuardedValueGraph.FiniteDecision.freshGraph_edge, projectNode_next]

/-- The finite algorithm computes the local rank from FreshNoCycle, including
fresh-to-old edges; no local rank or typing of projected units is supplied. -/
def allocationGuard {graph : Graph R} (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (fresh : Fin n → Value (Sum R (Fin n)) Empty) (hc : FreshNoCycle fresh) :
    GuardedValueGraph.Guarded (projectGraph (allocate graph fresh)) := by
  rw [project_allocation]
  exact GuardedValueGraph.FiniteDecision.allocateFiniteGuard guard (fun s => projectNode (fresh s)) hc

theorem allocation_guard_iff {graph : Graph R} (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (fresh : Fin n → Value (Sum R (Fin n)) Empty) :
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate graph fresh))) ↔ FreshNoCycle fresh := by
  rw [project_allocation]
  exact GuardedValueGraph.FiniteDecision.allocate_guard_iff guard (fun s => projectNode (fresh s))

def sourceFresh (capture : Nat → Value R Empty) (rhs : Fin n → HigherOrder.Value) :
    Fin n → Value (Sum R (Fin n)) Empty :=
  fun s => sourceCloseValue capture n (rhs s)

/-- Application to GVG-REC-RHS-1: every fresh node's typing is DERIVED from
the actual RHS derivation in the common source recursive context and separately
typed outer captures. The body uses exactly the same simultaneous substitution.
The only guard premise is the actual finite transparent-cycle criterion. -/
theorem source_rec_allocation {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → HigherOrder.Value)
    (hrhs : ∀ s, HigherOrder.ValueTyped (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : HigherOrder.CompTyped (sourceContext nu env) body a) :
    WellTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate graph (sourceFresh capture rhs)))) ∧
    CompTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseComp capture n body) a := by
  have hf : ∀ s, ValueTyped (joinTy xi nu) emptyTy emptyContext
      (sourceFresh capture rhs s) (nu s) :=
    fun s => sourceCloseValue_typed (hrhs s) hcapture
  exact ⟨allocate_typed hg _ hf, ⟨allocationGuard guard _ hcycle⟩,
    sourceCloseComp_typed hbody hcapture⟩

/-- The explicit-name source form also allows old graph references in RHS
code. This theorem consumes RHS derivations before closing, not pretyped fresh
nodes. The preceding theorem supplies that premise from the accepted source
grammar by the concrete prefix-splitting translation. -/
theorem named_rec_allocation {graph : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (guard : GuardedValueGraph.Guarded (projectGraph graph))
    (rhs : Fin n → Value R (Fin n))
    (hrhs : ∀ s, ValueTyped xi nu env (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (fun s => closeValue capture (rhs s)))
    (hbody : CompTyped xi nu env body a) :
    WellTyped (allocate graph (fun s => closeValue capture (rhs s))) (joinTy xi nu) ∧
    Nonempty (GuardedValueGraph.Guarded
      (projectGraph (allocate graph (fun s => closeValue capture (rhs s))))) ∧
    CompTyped (joinTy xi nu) emptyTy emptyContext (closeComp capture body) a :=
  ⟨allocate_typed hg _ (fun s => closeValue_typed (hrhs s) hcapture),
    ⟨allocationGuard guard _ hcycle⟩, closeComp_typed hbody hcapture⟩

/-- For a finite old graph, neither old nor fresh numeric ranks are inputs. -/
theorem finite_source_rec_allocation {graph : Graph (Fin m)}
    {xi : Fin m → Ty} {nu : Fin n → Ty}
    (hg : WellTyped graph xi) (hOld : GuardedValueGraph.FiniteDecision.NoCycle (projectGraph graph))
    (rhs : Fin n → HigherOrder.Value)
    (hrhs : ∀ s, HigherOrder.ValueTyped (sourceContext nu env) (rhs s) (nu s))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (hbody : HigherOrder.CompTyped (sourceContext nu env) body a) :
    WellTyped (allocate graph (sourceFresh capture rhs)) (joinTy xi nu) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate graph (sourceFresh capture rhs)))) ∧
    CompTyped (joinTy xi nu) emptyTy emptyContext (sourceCloseComp capture n body) a :=
  source_rec_allocation hg (GuardedValueGraph.FiniteDecision.guardOfNoCycle _ hOld) rhs hrhs hcapture hcycle hbody


/-- Binder equations expose the lambda consumer's separate outer scope. -/
theorem close_lambda (capture : Nat → Value R Empty)
    (mode receipt a b c body consumer) :
    closeValue (S := S) capture (.lambda mode receipt a b c body consumer) =
      .lambda mode receipt a b c
        (substComp (lift (closedCapture capture))
          (closeNamesComp Sum.inl Sum.inr body))
        (substAdapter (closedCapture capture)
          (closeNamesAdapter Sum.inl Sum.inr consumer)) := rfl

theorem close_adapter (capture : Nat → Value R Empty) (a b body paths views) :
    closeAdapter (S := S) capture (.mk a b body paths views) =
      .mk a b
        (substComp (lift (closedCapture capture))
          (closeNamesComp Sum.inl Sum.inr body)) paths views := rfl

theorem close_request (capture : Nat → Value R Empty) (op payload continuation) :
    closeComp (S := S) capture (.request op payload continuation) =
      .request op (closeValue capture payload)
        (substComp (lift (closedCapture capture))
          (closeNamesComp Sum.inl Sum.inr continuation)) := rfl

namespace Examples
def unitTy : Ty := .base .unit
def functionTy : Ty := .callable unitTy unitTy
def receipt : ReceiptTemplate := ⟨[], []⟩
def outer : Context := extend emptyContext unitTy
def oldGraph : Graph (Fin 1) := fun _ => .unit
def oldTypes : Fin 1 → Ty := fun _ => unitTy
def capture : Nat → Value (Fin 1) Empty := fun _ => .ref 0

theorem old_typed : WellTyped oldGraph oldTypes := fun _ => .unit

theorem capture_typed : CapturesTyped oldTypes outer capture := by
  intro i a hi
  cases i with
  | zero =>
      change some unitTy = some a at hi
      cases hi
      exact .ref 0
  | succ i => cases hi

def oldGuard : GuardedValueGraph.Guarded (projectGraph oldGraph) :=
  GuardedValueGraph.FiniteDecision.guardOfNoCycle _
    (GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl))

def other (s : Fin 2) : Fin 2 := if s.val = 0 then 1 else 0

/-- Both source lambdas call the opposite recursive name. They share the
same outer capture in the body and in the designated result consumer. -/
def mutualRhs (s : Fin 2) : HigherOrder.Value :=
  .lambda .computation receipt unitTy unitTy unitTy
    (.bind (.ret (.var 3))
      (.dynamicCall (.var ((other s).val + 2)) (.var 1)))
    (.mk unitTy unitTy (.bind (.ret (.var 3)) (.ret (.var 1))) [] [])

theorem mutualRhs_typed (s : Fin 2) :
    HigherOrder.ValueTyped (sourceContext (fun _ : Fin 2 => functionTy) outer)
      (mutualRhs s) functionTy := by
  apply HigherOrder.ValueTyped.lambdaComputation
  · apply HigherOrder.CompTyped.bind (a := unitTy)
    · exact .ret (.var rfl)
    · exact .dynamicCall
        (.var (source_recursive_lookup (fun _ : Fin 2 => functionTy) outer (other s)))
        (.var rfl)
  · exact .mk (.bind (a := unitTy) (.ret (.var rfl)) (.ret (.var rfl)))

def mutualFresh := sourceFresh capture mutualRhs

/-- Actual allocated code, including two independent local binders and the
shared old reference. This equation is more than a pretyped reference example. -/
theorem mutualFresh_equation (s : Fin 2) :
    mutualFresh s =
      .lambda .computation receipt unitTy unitTy unitTy
        (.bind (.ret (.ref (.inl 0)))
          (.dynamicCall (.ref (.inr (other s))) (.var 1)))
        (.mk unitTy unitTy
          (.bind (.ret (.ref (.inl 0))) (.ret (.var 1))) [] []) := by
  have hs : s = 0 ∨ s = 1 := by
    have hb := s.isLt
    by_cases hz : s.val = 0
    · exact .inl (Fin.ext hz)
    · exact .inr (Fin.ext (by omega))
  rcases hs with rfl | rfl <;> rfl

theorem mutualFresh_noCycle : FreshNoCycle mutualFresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem mutual_allocation :
    WellTyped (allocate oldGraph mutualFresh) (joinTy oldTypes (fun _ => functionTy)) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate oldGraph mutualFresh))) ∧
    CompTyped (joinTy oldTypes (fun _ => functionTy)) emptyTy emptyContext
      (sourceCloseComp capture 2 (.ret (.var 0))) functionTy :=
  source_rec_allocation old_typed oldGuard mutualRhs mutualRhs_typed capture_typed
    mutualFresh_noCycle (.ret (.var rfl))

def operation : OperationInstance := ⟨37, [functionTy], unitTy, functionTy⟩

/-- A response binder survives both recursive substitution and outer capture.
The continuation uses the recursive delayed node and returns its original
higher-order response after a local bind. -/
def responseRhs : HigherOrder.Value :=
  .delay (.request operation (.var 1)
    (.bind (.ret (.var 1)) (.ret (.var 1))))

theorem responseRhs_typed :
    HigherOrder.ValueTyped
      (sourceContext (fun _ : Fin 1 => .thunk functionTy) outer)
      responseRhs (.thunk functionTy) :=
  .delay (.request (.var rfl)
    (.bind (a := .thunk functionTy) (.ret (.var rfl)) (.ret (.var rfl))))

theorem response_closed :
    sourceCloseValue capture 1 responseRhs =
      .delay (.request operation (.ref (.inl 0))
        (.bind (.ret (.ref (.inr 0))) (.ret (.var 1)))) := rfl

theorem response_closed_typed :
    ValueTyped (joinTy oldTypes (fun _ : Fin 1 => .thunk functionTy))
      emptyTy emptyContext (sourceCloseValue capture 1 responseRhs) (.thunk functionTy) :=
  sourceCloseValue_typed responseRhs_typed capture_typed

/-- A source RHS that is an outer captured old reference is a legal
fresh-to-old transparent edge, with no rank supplied. -/
def oldAliasRhs : Fin 1 → HigherOrder.Value := fun _ => .var 1
def oldAliasFresh := sourceFresh capture oldAliasRhs

theorem oldAlias_equation (s : Fin 1) :
    oldAliasFresh s = .ref (.inl 0) := rfl

theorem oldAlias_noCycle : FreshNoCycle oldAliasFresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem oldAlias_allocation :
    WellTyped (allocate oldGraph oldAliasFresh) (joinTy oldTypes (fun _ => unitTy)) ∧
    Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate oldGraph oldAliasFresh))) ∧
    CompTyped (joinTy oldTypes (fun _ => unitTy)) emptyTy emptyContext
      (sourceCloseComp capture 1 (.ret (.var 0))) unitTy :=
  source_rec_allocation old_typed oldGuard oldAliasRhs (fun _ => .var rfl)
    capture_typed oldAlias_noCycle (.ret (.var rfl))

def aliasRhs : Fin 1 → HigherOrder.Value := fun _ => .var 0
def aliasFresh := sourceFresh capture aliasRhs

/-- The source typing derivation alone permits x=x at any type. The separate
guard rejects this actual source-closed alias cycle. -/
theorem aliasRhs_typed (a : Ty) (s : Fin 1) :
    HigherOrder.ValueTyped (sourceContext (fun _ : Fin 1 => a) outer) (aliasRhs s) a :=
  .var rfl

theorem alias_cycle_rejected : ¬ FreshNoCycle aliasFresh := by
  intro hc
  exact hc 0 (.edge rfl)

theorem alias_allocation_unguarded :
    ¬ Nonempty (GuardedValueGraph.Guarded (projectGraph (allocate oldGraph aliasFresh))) :=
  fun h => alias_cycle_rejected ((allocation_guard_iff oldGuard aliasFresh).mp h)

end Examples

end YulangClosure.HigherOrderGraph
