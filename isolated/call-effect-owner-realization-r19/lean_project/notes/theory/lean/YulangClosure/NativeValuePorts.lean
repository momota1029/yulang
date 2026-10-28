import YulangClosure.NativeContextExpansion
import YulangClosure.NativeRecordPlan

/-!
Actual structured Value child admission.  The complete relation key, the native
source indices, the inherited post-check Context and the full deferred Function
demand are retained.  The two-stage child loop records admission before enqueue.
This is an allocation-success transcription of the named native constructors;
it does not supply Value semantics, diagnostic acceptance or source typing.
-/
namespace YulangClosure.NativeValuePorts

open NativeContextExpansion (Expr ScopedDemand)
open NativeMergeExpansion (Endpoint renameEndpoint)

inductive ValueEndpoint where
  | bottomPositive | bottomNegative | topNegative
  | intPositive | intNegative | unitPositive | boolPositive | strPositive
  | unitNegative | boolNegative | strNegative
  | row (id : Nat)
  | positiveFunction (term : Nat) | negativeFunction (term : Nat)
  | positiveVariant (term : Nat) | negativeVariant (term : Nat)
  | positiveRecord (term : Nat) | negativeRecord (term : Nat)
  | positiveTuple (term arity : Nat) | negativeTuple (term arity : Nat)
  deriving DecidableEq, Repr

def ValueEndpoint.rename (q : Nat → Nat) : ValueEndpoint → ValueEndpoint
  | .row id => .row (q id)
  | other => other

inductive Pair where
  | value (lower upper : ValueEndpoint)
  | effect (lower upper : Endpoint)
  deriving DecidableEq, Repr

def Pair.rename (qv qe : Nat → Nat) : Pair → Pair
  | .value lower upper => .value (lower.rename qv) (upper.rename qv)
  | .effect lower upper => .effect (renameEndpoint qe lower) (renameEndpoint qe upper)

structure Flow where
  transformer : Nat := 0
  demand : Option ScopedDemand := none
  deriving DecidableEq, Repr

structure Key where
  pair : Pair
  context : Nat
  sources : Option Nat
  flow : Flow
  deriving DecidableEq, Repr

inductive FunctionField where
  | argument | argumentEffect | resultEffect | result
  deriving DecidableEq, Repr

inductive Port where
  | function (field : FunctionField)
  | tuple (index : Nat)
  | record (lowerIndex upperIndex : Nat)
  | variant (lowerIndex upperIndex payloadIndex : Nat)
  deriving DecidableEq, Repr

def Port.swaps : Port → Bool
  | .function .argument | .function .argumentEffect => true
  | _ => false

/-- The complete canonical transformer data, including release tombstones.
The present owner constructs only the exact stamp/protect entries below. -/
structure Protection where
  scope : Nat
  keepInitial : Bool
  missing : List Nat
  deriving DecidableEq, Repr

structure Transformer where
  stamped : List Nat
  scopes : List Protection
  deriving DecidableEq, Repr

def Transformer.identity : Transformer := ⟨[], []⟩
def Transformer.stamp (input : Nat) : Transformer := ⟨[input], []⟩
def Transformer.protect (scope input : Nat) : Transformer :=
  ⟨[], [⟨scope, true, [input]⟩]⟩

def Transformer.input (t : Transformer) (initial : Nat → Prop) (input : Nat) : Prop :=
  initial input ∨ input ∈ t.stamped

def Transformer.protection (t : Transformer) (inputs scopes : Nat → Prop)
    (scope : Nat) : Prop :=
  match t.scopes.find? (fun entry => entry.scope = scope) with
  | none => scopes scope
  | some entry => (entry.keepInitial = true ∧ scopes scope) ∨
      ∃ input ∈ entry.missing, ¬ inputs input

theorem stamp_input_exact (input i : Nat) (initial : Nat → Prop) :
    (Transformer.stamp input).input initial i ↔ initial i ∨ i = input := by
  simp [Transformer.input, Transformer.stamp]

theorem stamp_preserves_protections (input scope : Nat) (inputs scopes : Nat → Prop) :
    (Transformer.stamp input).protection inputs scopes scope ↔ scopes scope := Iff.rfl

theorem protect_body_exact (scope input : Nat) (inputs scopes : Nat → Prop) :
    (Transformer.protect scope input).protection inputs scopes scope ↔
      scopes scope ∨ ¬ inputs input := by
  simp [Transformer.protection, Transformer.protect]

theorem protect_other_exact {scope other input : Nat} (different : other ≠ scope)
    (inputs scopes : Nat → Prop) :
    (Transformer.protect scope input).protection inputs scopes other ↔ scopes other := by
  simp [Transformer.protection, Transformer.protect, Ne.symm different]

theorem protect_preserves_inputs (scope input i : Nat) (inputs : Nat → Prop) :
    (Transformer.protect scope input).input inputs i ↔ inputs i := by
  simp [Transformer.input, Transformer.protect]

/-- Zero-based interning, with all equality data retained. Native hash buckets
are only an index: their equality check is equality of the entire object. -/
def intern [DecidableEq α] (items : List α) (value : α) : List α × Nat :=
  if value ∈ items then (items, items.idxOf value)
  else (items ++ [value], items.length)

def Extends (before after : List α) : Prop :=
  ∀ (index : Nat) (value : α), before[index]? = some value → after[index]? = some value

theorem extends_refl (items : List α) : Extends items items := fun _ _ h => h

theorem extends_trans {a b c : List α} (first : Extends a b) (second : Extends b c) :
    Extends a c := fun i x h => second i x (first i x h)

theorem intern_found [DecidableEq α] (items : List α) (value : α) :
    (intern items value).1[(intern items value).2]? = some value := by
  unfold intern
  split
  next present =>
    rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem present)]
    simp
  next => simp

theorem intern_extends [DecidableEq α] (items : List α) (value : α) :
    Extends items (intern items value).1 := by
  intro index old found
  unfold intern
  split
  · exact found
  · obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
    simpa [List.getElem?_append_left bound] using found

theorem intern_length (items : List α) [DecidableEq α] (value : α) :
    items.length ≤ (intern items value).1.length := by
  unfold intern
  split <;> simp

theorem intern_reuse_exact [DecidableEq α] (items : List α) (first second : α)
    (same : (intern items first).2 = (intern (intern items first).1 second).2) :
    first = second := by
  have old := intern_extends (intern items first).1 second _ _ (intern_found items first)
  rw [same, intern_found] at old
  exact (Option.some.inj old).symm

structure Arena where
  contexts : List Expr := []
  transformers : List Transformer := []
  relations : List Key := []
  deriving DecidableEq, Repr

def Arena.context (arena : Arena) (node : Expr) : Arena × Nat :=
  let result := intern arena.contexts node
  ({arena with contexts := result.1}, result.2 + 1)

def Arena.transformer (arena : Arena) (transformer : Transformer) : Arena × Nat :=
  if transformer = .identity then (arena, 0)
  else
    let result := intern arena.transformers transformer
    ({arena with transformers := result.1}, result.2 + 1)

def Arena.relation (arena : Arena) (key : Key) : Arena × Nat :=
  let result := intern arena.relations key
  ({arena with relations := result.1}, result.2)

def Arena.contextAt (arena : Arena) (id : Nat) : Option Expr :=
  if id = 0 then none else arena.contexts[id - 1]?

def Arena.transformerAt (arena : Arena) (id : Nat) : Option Transformer :=
  if id = 0 then some .identity else arena.transformers[id - 1]?

def Arena.Extends (before after : Arena) : Prop :=
  NativeValuePorts.Extends before.contexts after.contexts ∧
  NativeValuePorts.Extends before.transformers after.transformers ∧
  NativeValuePorts.Extends before.relations after.relations

theorem arena_extends_refl (arena : Arena) : arena.Extends arena :=
  ⟨extends_refl _, extends_refl _, extends_refl _⟩

theorem arena_extends_trans {a b c : Arena} (first : a.Extends b) (second : b.Extends c) :
    a.Extends c :=
  ⟨extends_trans first.1 second.1, extends_trans first.2.1 second.2.1,
    extends_trans first.2.2 second.2.2⟩

theorem context_constructed (arena : Arena) (node : Expr) :
    (arena.context node).1.contextAt (arena.context node).2 = some node ∧
    arena.Extends (arena.context node).1 := by
  constructor
  · simpa [Arena.context, Arena.contextAt] using intern_found arena.contexts node
  · exact ⟨intern_extends _ _, extends_refl _, extends_refl _⟩

theorem transformer_constructed (arena : Arena) (transformer : Transformer) :
    (arena.transformer transformer).1.transformerAt (arena.transformer transformer).2 =
      some transformer ∧ arena.Extends (arena.transformer transformer).1 := by
  unfold Arena.transformer
  split
  next identity => subst transformer; exact ⟨rfl, arena_extends_refl _⟩
  next =>
    exact ⟨by simpa [Arena.transformerAt] using intern_found arena.transformers transformer,
      ⟨extends_refl _, intern_extends _ _, extends_refl _⟩⟩

theorem relation_constructed (arena : Arena) (key : Key) :
    (arena.relation key).1.relations[(arena.relation key).2]? = some key ∧
    arena.Extends (arena.relation key).1 :=
  ⟨intern_found _ _, ⟨extends_refl _, extends_refl _, intern_extends _ _⟩⟩

def contextInputs : Expr → List Nat
  | .prefix _ input | .suffix input _ | .swap input | .both input _ | .without input => [input]
  | .replay lower upper => [lower, upper]

/-- A Context child is Identity or an already allocated strictly earlier ID. -/
def ContextsFormed (contexts : List Expr) : Prop :=
  ∀ (index : Nat) (node : Expr), contexts[index]? = some node →
    ∀ input ∈ contextInputs node, input ≤ index

theorem context_index_bound (arena : Arena) (node : Expr) :
    (arena.context node).2 ≤ (arena.context node).1.contexts.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp (intern_found arena.contexts node)
  exact bound

theorem context_preserves_formation {arena : Arena} {node : Expr}
    (formed : ContextsFormed arena.contexts)
    (inputs : ∀ input ∈ contextInputs node, input ≤ arena.contexts.length) :
    ContextsFormed (arena.context node).1.contexts := by
  unfold Arena.context intern
  split
  · exact formed
  · intro index actual found input member
    by_cases earlier : index < arena.contexts.length
    · rw [List.getElem?_append_left earlier] at found
      exact formed index actual found input member
    · obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
      have same : index = arena.contexts.length := by simp only [List.length_append, List.length_singleton] at bound; omega
      subst index
      have actualSame : actual = node := by
        simpa only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] using found.symm
      exact inputs input (actualSame ▸ member)

theorem context_length (arena : Arena) (node : Expr) :
    arena.contexts.length ≤ (arena.context node).1.contexts.length := intern_length _ _

theorem context_kept {before after : Arena} (extension : before.Extends after)
    {id : Nat} {node : Expr} (found : before.contextAt id = some node) :
    after.contextAt id = some node := by
  unfold Arena.contextAt at found ⊢
  split at found
  · cases found
  · rename_i nonzero
    simp only [nonzero, ↓reduceIte]
    exact extension.1 _ _ found

theorem transformer_kept {before after : Arena} (extension : before.Extends after)
    {id : Nat} {transformer : Transformer} (found : before.transformerAt id = some transformer) :
    after.transformerAt id = some transformer := by
  unfold Arena.transformerAt at found ⊢
  split at found
  · rename_i zero; simpa [zero] using found
  · rename_i nonzero
    simp only [nonzero, ↓reduceIte]
    exact extension.2.1 _ _ found

/-- The source-local prefix is interned before the inherited Function operation,
then wraps that operation. The native post-check ID is an explicit argument. -/
def buildContext (arena : Arena) (localWeight : Option Nat) (post : Nat) (swap : Bool) : Arena × Nat :=
  let first := match localWeight with
    | none => (arena, 0)
    | some weight => arena.context (.prefix weight 0)
  let inherited := if swap = true ∧ post ≠ 0 then first.1.context (.swap post) else (first.1, post)
  match localWeight with
  | none => inherited
  | some weight => inherited.1.context (.prefix weight inherited.2)

def ContextResult (arena : Arena) (localWeight : Option Nat) (post : Nat) (swap : Bool) (id : Nat) : Prop :=
  ∃ inherited,
    (if swap = true ∧ post ≠ 0 then arena.contextAt inherited = some (.swap post)
     else inherited = post) ∧
    (match localWeight with
     | none => id = inherited
     | some weight => arena.contextAt id = some (.prefix weight inherited))

theorem build_context_extends (arena : Arena) (localWeight : Option Nat) (post : Nat) (swap : Bool) :
    arena.Extends (buildContext arena localWeight post swap).1 := by
  unfold buildContext
  cases localWeight with
  | none =>
      simp only
      split
      · exact (context_constructed _ _).2
      · exact arena_extends_refl _
  | some weight =>
      simp only
      split
      · exact arena_extends_trans (context_constructed _ _).2
          (arena_extends_trans (context_constructed _ _).2 (context_constructed _ _).2)
      · exact arena_extends_trans (context_constructed _ _).2 (context_constructed _ _).2

theorem build_context_exact (arena : Arena) (localWeight : Option Nat) (post : Nat) (swap : Bool) :
    ContextResult (buildContext arena localWeight post swap).1 localWeight post swap
      (buildContext arena localWeight post swap).2 := by
  unfold buildContext ContextResult
  cases localWeight with
  | none =>
      simp only
      split
      next yes =>
        have condition : swap = true ∧ post ≠ 0 := by simpa using yes
        exact ⟨_, by simpa [condition] using (context_constructed arena (.swap post)).1, rfl⟩
      next no =>
        have condition : ¬ (swap = true ∧ post ≠ 0) := by simpa using no
        exact ⟨post, by simp, rfl⟩
  | some weight =>
      simp only
      split
      next yes =>
        have condition : swap = true ∧ post ≠ 0 := by simpa using yes
        refine ⟨_, ?_, (context_constructed _ _).1⟩
        exact context_kept (context_constructed _ _).2 (context_constructed _ _).1
      next no =>
        have condition : ¬ (swap = true ∧ post ≠ 0) := by simpa using no
        exact ⟨post, by simp, (context_constructed _ _).1⟩

theorem build_context_formed {arena : Arena} {weight : Option Nat} {post : Nat} {swap : Bool}
    (formed : ContextsFormed arena.contexts) (validPost : post ≤ arena.contexts.length) :
    ContextsFormed (buildContext arena weight post swap).1.contexts ∧
      (buildContext arena weight post swap).2 ≤ (buildContext arena weight post swap).1.contexts.length := by
  unfold buildContext
  cases weight with
  | none =>
      simp only
      split
      · exact ⟨context_preserves_formation formed (by simpa [contextInputs] using validPost),
          context_index_bound _ _⟩
      · exact ⟨formed, validPost⟩
  | some weight =>
      simp only
      have first : ContextsFormed (arena.context (.prefix weight 0)).1.contexts :=
        context_preserves_formation formed (by simp [contextInputs])
      have inheritedBound := Nat.le_trans validPost (context_length arena (.prefix weight 0))
      split
      · have second := context_preserves_formation first
          (node := Expr.swap post) (by simpa [contextInputs] using inheritedBound)
        exact ⟨context_preserves_formation second
          (by simpa [contextInputs] using context_index_bound (arena.context (.prefix weight 0)).1 (.swap post)),
          context_index_bound _ _⟩
      · exact ⟨context_preserves_formation first (by simpa [contextInputs] using inheritedBound),
          context_index_bound _ _⟩

def genuineDemand (parent : Key) (demand : ScopedDemand) : Prop :=
  match parent.pair with
  | .value _ (.negativeFunction root) => root = demand.root
  | _ => False

instance (parent : Key) (demand : ScopedDemand) : Decidable (genuineDemand parent demand) := by
  unfold genuineDemand
  cases parent.pair with
  | effect => infer_instance
  | value lower upper => cases upper <;> infer_instance

/-- Function entry consumes the deferred demand exactly once. Other structural
ports preserve its complete five-field record, without a root-only projection. -/
def buildFlow (arena : Arena) (parent : Key) (port : Port) : Option (Arena × Flow) :=
  match port with
  | .function field =>
      if parent.flow.transformer ≠ 0 then none else
      match parent.flow.demand with
      | none => some (arena, parent.flow)
      | some demand =>
          if ¬ genuineDemand parent demand then none else
          match field with
          | .argument | .result => some (arena, ⟨0, none⟩)
          | .argumentEffect =>
              let result := arena.transformer (.stamp demand.inputRoute)
              some (result.1, ⟨result.2, none⟩)
          | .resultEffect =>
              let result := arena.transformer (.protect demand.outputScope demand.inputRoute)
              some (result.1, ⟨result.2, none⟩)
  | _ => some (arena, parent.flow)

def FlowResult (arena : Arena) (parent : Key) (port : Port) (flow : Flow) : Prop :=
  match port with
  | .function field =>
      parent.flow.transformer = 0 ∧
      (match parent.flow.demand with
       | none => flow = parent.flow
       | some demand => genuineDemand parent demand ∧ flow.demand = none ∧
           match field with
           | .argument | .result => flow.transformer = 0
           | .argumentEffect => arena.transformerAt flow.transformer = some (.stamp demand.inputRoute)
           | .resultEffect => arena.transformerAt flow.transformer =
               some (.protect demand.outputScope demand.inputRoute))
  | _ => flow = parent.flow

theorem build_flow_exact {arena after : Arena} {parent : Key} {port : Port} {flow : Flow}
    (computed : buildFlow arena parent port = some (after, flow)) :
    arena.Extends after ∧ FlowResult after parent port flow := by
  cases port with
  | tuple index => cases computed; exact ⟨arena_extends_refl _, rfl⟩
  | record lower upper => cases computed; exact ⟨arena_extends_refl _, rfl⟩
  | variant lower upper payload => cases computed; exact ⟨arena_extends_refl _, rfl⟩
  | function field =>
      by_cases zero : parent.flow.transformer = 0
      · cases hd : parent.flow.demand with
        | none =>
            simp only [buildFlow, zero, ne_eq, not_true_eq_false, ↓reduceIte, hd] at computed
            cases computed
            exact ⟨arena_extends_refl _, zero, by simp [hd]⟩
        | some demand =>
            by_cases genuine : genuineDemand parent demand
            · simp only [buildFlow, zero, ne_eq, not_true_eq_false, ↓reduceIte, hd,
                genuine] at computed
              cases field <;> cases computed
              · exact ⟨arena_extends_refl _, zero, by simp [hd, genuine]⟩
              · refine ⟨(transformer_constructed _ _).2, zero, ?_⟩
                simp only [hd]
                exact ⟨genuine, True.intro, (transformer_constructed _ _).1⟩
              · refine ⟨(transformer_constructed _ _).2, zero, ?_⟩
                simp only [hd]
                exact ⟨genuine, True.intro, (transformer_constructed _ _).1⟩
              · exact ⟨arena_extends_refl _, zero, by simp [hd, genuine]⟩
            · simp [buildFlow, zero, hd, genuine] at computed
      · simp [buildFlow, zero] at computed

theorem flow_result_kept {before after : Arena} (extension : before.Extends after)
    {parent : Key} {port : Port} {flow : Flow} (valid : FlowResult before parent port flow) :
    FlowResult after parent port flow := by
  cases port with
  | tuple | record | variant => exact valid
  | function field =>
      obtain ⟨zero, rest⟩ := valid
      refine ⟨zero, ?_⟩
      cases hd : parent.flow.demand with
      | none => simpa [hd] using rest
      | some demand =>
          simp only [hd] at rest ⊢
          obtain ⟨genuine, consumed, transform⟩ := rest
          refine ⟨genuine, consumed, ?_⟩
          cases field with
          | argument | result => exact transform
          | argumentEffect | resultEffect => exact transformer_kept extension transform

theorem context_result_kept {before after : Arena} (extension : before.Extends after)
    {weight : Option Nat} {post id : Nat} {swap : Bool}
    (valid : ContextResult before weight post swap id) :
    ContextResult after weight post swap id := by
  obtain ⟨inherited, operation, outer⟩ := valid
  refine ⟨inherited, ?_, ?_⟩
  · by_cases condition : swap = true ∧ post ≠ 0
    · rw [ite_eq_left condition] at operation ⊢
      exact context_kept extension operation
    · rw [ite_eq_right condition] at operation ⊢
      exact operation
  · cases weight with
    | none => exact outer
    | some => exact context_kept extension outer

/-- A missing view is an unavailable table read, distinct from a valid view
whose closed-weight field is absent. Value tasks have no local Effect prefix. -/
def sourceWeight (views : Nat → Option (Option Nat)) : Pair → Option (Option Nat)
  | .effect _ (.allowance view) => views view
  | _ => some none

def Allowed (key : Key) : Prop :=
  match key.pair with
  | .value _ _ => key.flow.transformer = 0
  | .effect lower upper => key.flow.demand = none ∧
      (key.flow.transformer = 0 ∨ lower ≠ upper)

instance (key : Key) : Decidable (Allowed key) := by
  unfold Allowed
  cases key.pair <;> infer_instance

structure Child where
  port : Port
  task : Pair
  deriving DecidableEq, Repr

structure Receipt where
  parent : Key
  child : Key
  relation : Nat
  port : Port
  derived : Bool
  deriving DecidableEq, Repr

/-- The typed dependency keeps all original indices. A Derived dependency is
additional; it does not replace Function/Tuple/Record/Variant provenance. -/
inductive Dependency where
  | derived (parent child : Key)
  | port (parent child : Key) (port : Port)
  deriving DecidableEq, Repr

def Receipt.dependencies (receipt : Receipt) : List Dependency :=
  (if receipt.derived then [.derived receipt.parent receipt.child] else []) ++
    [.port receipt.parent receipt.child receipt.port]

def admit (arena : Arena) (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) (child : Child) : Option (Arena × Receipt) := do
  let pair := child.task.rename qv qe
  let weight ← sourceWeight views pair
  let context := buildContext arena weight post child.port.swaps
  let (flowArena, flow) ← buildFlow context.1 parent child.port
  let key := Key.mk pair context.2 parent.sources flow
  if ¬ Allowed key then none else
    let relation := flowArena.relation key
    some (relation.1, ⟨parent, key, relation.2, child.port, derived⟩)

structure AdmissionResult (arena : Arena) (views : Nat → Option (Option Nat))
    (qv qe : Nat → Nat) (parent : Key) (post : Nat) (derived : Bool)
    (child : Child) (receipt : Receipt) : Prop where
  parent_same : receipt.parent = parent
  port_same : receipt.port = child.port
  derived_same : receipt.derived = derived
  pair_exact : receipt.child.pair = child.task.rename qv qe
  sources_same : receipt.child.sources = parent.sources
  context_exact : ∃ weight, sourceWeight views (child.task.rename qv qe) = some weight ∧
    ContextResult arena weight post child.port.swaps receipt.child.context
  flow_exact : FlowResult arena parent child.port receipt.child.flow
  guards : Allowed receipt.child
  registered : arena.relations[receipt.relation]? = some receipt.child

theorem admit_constructs {arena after : Arena} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {child : Child} {receipt : Receipt}
    (computed : admit arena views qv qe parent post derived child = some (after, receipt)) :
    arena.Extends after ∧ AdmissionResult after views qv qe parent post derived child receipt := by
  unfold admit at computed
  obtain ⟨weight, hw, computed⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨⟨flowArena, flow⟩, hf, computed⟩ := Option.bind_eq_some_iff.mp computed
  by_cases allowed : Allowed ⟨child.task.rename qv qe,
      (buildContext arena weight post child.port.swaps).2, parent.sources, flow⟩
  · simp only [allowed, not_true_eq_false, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq] at computed
    rcases computed with ⟨rfl, rfl⟩
    have flowFacts := build_flow_exact hf
    have relationFacts := relation_constructed flowArena
      ⟨child.task.rename qv qe, (buildContext arena weight post child.port.swaps).2,
        parent.sources, flow⟩
    refine ⟨arena_extends_trans (build_context_extends _ _ _ _)
      (arena_extends_trans flowFacts.1 relationFacts.2),
      rfl, rfl, rfl, rfl, rfl, ?_, ?_, allowed, relationFacts.1⟩
    · exact ⟨weight, hw, context_result_kept
        (arena_extends_trans flowFacts.1 relationFacts.2) (build_context_exact _ _ _ _)⟩
    · exact flow_result_kept relationFacts.2 flowFacts.2
  · simp [allowed] at computed

theorem structural_demand_preserved {arena : Arena} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {child : Child} {receipt : Receipt}
    (valid : AdmissionResult arena views qv qe parent post derived child receipt)
    (structural : ∀ field, child.port ≠ .function field) :
    receipt.child.flow = parent.flow := by
  have flow := valid.flow_exact
  cases hp : child.port with
  | function field => exact False.elim (structural field hp)
  | tuple | record | variant => simpa [FlowResult, hp] using flow

theorem every_port_dependency (receipt : Receipt) :
    Dependency.port receipt.parent receipt.child receipt.port ∈ receipt.dependencies := by
  simp [Receipt.dependencies]

theorem derived_dependency_iff (receipt : Receipt) :
    Dependency.derived receipt.parent receipt.child ∈ receipt.dependencies ↔
      receipt.derived = true := by
  cases hd : receipt.derived <;> simp [Receipt.dependencies, hd]

theorem nonidentity_effect_self_rejected (pairContext : Nat)
    (sources : Option Nat) (flow : Flow) (endpoint : Endpoint)
    (nonidentity : flow.transformer ≠ 0) :
    ¬ Allowed ⟨.effect endpoint endpoint, pairContext, sources, flow⟩ := by
  simp [Allowed, nonidentity]

structure FunctionTerms where
  argument : Nat
  argumentEffect : Nat
  resultEffect : Nat
  result : Nat
  deriving DecidableEq, Repr

structure TermEndpoints where
  positiveValue : Nat → ValueEndpoint
  negativeValue : Nat → ValueEndpoint
  positiveEffect : Nat → Endpoint
  negativeEffect : Nat → Endpoint

/-- Exact source order and variance of the four native Function children.
These term lookups are raw store readbacks, not semantic comparison oracles. -/
def functionChildren (terms : TermEndpoints) (lower upper : FunctionTerms) : List Child :=
  [⟨.function .argument,
      .value (terms.positiveValue upper.argument) (terms.negativeValue lower.argument)⟩,
   ⟨.function .argumentEffect,
      .effect (terms.positiveEffect upper.argumentEffect) (terms.negativeEffect lower.argumentEffect)⟩,
   ⟨.function .resultEffect,
      .effect (terms.positiveEffect lower.resultEffect) (terms.negativeEffect upper.resultEffect)⟩,
   ⟨.function .result,
      .value (terms.positiveValue lower.result) (terms.negativeValue upper.result)⟩]

theorem function_children_whole (terms : TermEndpoints) (lower upper : FunctionTerms) :
    (functionChildren terms lower upper).map Child.port =
      [.function .argument, .function .argumentEffect, .function .resultEffect, .function .result] ∧
    (functionChildren terms lower upper).length = 4 := ⟨rfl, rfl⟩

def tupleChildren (terms : TermEndpoints) (lowerArity upperArity : Nat)
    (lower upper : List Nat) : Option (List Child) :=
  if lowerArity = upperArity ∧ lower.length = lowerArity ∧ upper.length = upperArity then
    some ((lower.zip upper).zipIdx.map fun (pair, index) =>
      ⟨.tuple index, .value (terms.positiveValue pair.1) (terms.negativeValue pair.2)⟩)
  else none

theorem tuple_children_exact {terms : TermEndpoints} {lowerArity upperArity : Nat}
    {lower upper : List Nat} {children : List Child}
    (computed : tupleChildren terms lowerArity upperArity lower upper = some children) :
    lowerArity = upperArity ∧ lower.length = lowerArity ∧ upper.length = upperArity ∧
    children.length = lowerArity ∧
    ∀ (index lo hi : Nat), lower[index]? = some lo → upper[index]? = some hi →
      children[index]? = some ⟨.tuple index, .value (terms.positiveValue lo) (terms.negativeValue hi)⟩ := by
  unfold tupleChildren at computed
  split at computed
  next formed =>
    cases computed
    obtain ⟨same, low, high⟩ := formed
    refine ⟨same, low, high, by simp [low, high, same], ?_⟩
    intro index lo hi foundLow foundHigh
    have zipped : (lower.zip upper)[index]? = some (lo, hi) :=
      List.getElem?_zip_eq_some.mpr ⟨foundLow, foundHigh⟩
    simp [List.getElem?_zipIdx, zipped]
  next => cases computed

def recordChild (terms : TermEndpoints) (hole : NativeRecordPlan.Hole Key Nat) : Child :=
  ⟨.record hole.lowerIndex hole.upperIndex,
    .value (terms.positiveValue hole.sourceSpec.ty) (terms.negativeValue hole.targetField.2.ty)⟩

/-- Missing-field diagnostics and presence-unavailable branches retain the
original distinction in `NativeRecordPlan`; neither publishes a prefix. -/
def recordChildren (terms : TermEndpoints) (boundary : Key)
    (lower upper : List (RecordBoundary.Field Nat)) :
    Except NativeRecordPlan.Failure (List Child) :=
  (NativeRecordPlan.shape boundary lower 0 upper).map fun slots =>
    (NativeRecordPlan.children slots).map (recordChild terms)

theorem record_children_exact {terms : TermEndpoints} {boundary : Key}
    {lower upper : List (RecordBoundary.Field Nat)} {children : List Child}
    (computed : recordChildren terms boundary lower upper = .ok children) :
    ∃ slots, NativeRecordPlan.shape boundary lower 0 upper = .ok slots ∧
      NativeRecordPlan.ValidShape lower boundary 0 upper slots ∧
      children = (NativeRecordPlan.children slots).map (recordChild terms) := by
  unfold recordChildren at computed
  cases shaped : NativeRecordPlan.shape boundary lower 0 upper with
  | error failure => simp [shaped, Except.map] at computed
  | ok slots =>
      simp only [shaped, Except.map, Except.ok.injEq] at computed
      exact ⟨slots, rfl, NativeRecordPlan.shape_valid shaped, computed.symm⟩

structure Alternative where
  tag : Nat
  payloads : List Nat
  deriving DecidableEq, Repr

def matching (lower upper : Alternative) : Bool :=
  decide (lower.tag = upper.tag ∧ lower.payloads.length = upper.payloads.length)

def variantArmChildren (terms : TermEndpoints) (lowerIndex : Nat)
    (lower : Alternative) (upper : List Alternative) : List Child :=
  upper.zipIdx.flatMap fun (expected, upperIndex) =>
    if matching lower expected then
      (lower.payloads.zip expected.payloads).zipIdx.map fun (pair, payloadIndex) =>
        ⟨.variant lowerIndex upperIndex payloadIndex,
          .value (terms.positiveValue pair.1) (terms.negativeValue pair.2)⟩
    else []

def variantChildren (terms : TermEndpoints) (upper : List Alternative) :
    Nat → List Alternative → Except Nat (List Child)
  | _, [] => .ok []
  | index, actual :: rest =>
      if upper.any (matching actual) then
        (variantChildren terms upper (index + 1) rest).map
          (variantArmChildren terms index actual upper ++ ·)
      else .error index

theorem variant_arm_all_matches {terms : TermEndpoints} {lowerIndex upperIndex payloadIndex : Nat}
    {lower expected : Alternative} {upper : List Alternative} {lo hi : Nat}
    (expectedAt : upper[upperIndex]? = some expected)
    (same : matching lower expected = true)
    (lowerAt : lower.payloads[payloadIndex]? = some lo)
    (upperAt : expected.payloads[payloadIndex]? = some hi) :
    Child.mk (.variant lowerIndex upperIndex payloadIndex)
      (.value (terms.positiveValue lo) (terms.negativeValue hi)) ∈
      variantArmChildren terms lowerIndex lower upper := by
  apply List.mem_flatMap.mpr
  refine ⟨(expected, upperIndex), ?_, ?_⟩
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr expectedAt
  · simp only [same, ↓reduceIte]
    apply List.mem_map.mpr
    exact ⟨((lo, hi), payloadIndex), List.mk_mem_zipIdx_iff_getElem?.mpr
      (List.getElem?_zip_eq_some.mpr ⟨lowerAt, upperAt⟩), rfl⟩

theorem variant_children_no_omission {terms : TermEndpoints} {upper lower : List Alternative}
    {start : Nat} {children : List Child}
    (computed : variantChildren terms upper start lower = .ok children) :
    ∀ (offset : Nat) (actual : Alternative), lower[offset]? = some actual →
      ∀ child ∈ variantArmChildren terms (start + offset) actual upper, child ∈ children := by
  induction lower generalizing start children with
  | nil => intro offset actual found; simp at found
  | cons first rest ih =>
      unfold variantChildren at computed
      split at computed
      next admittedFamily =>
        cases tail : variantChildren terms upper (start + 1) rest with
        | error failure => simp [tail, Except.map] at computed
        | ok following =>
            simp only [tail, Except.map, Except.ok.injEq] at computed
            subst children
            intro offset actual found child member
            cases offset with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst actual
                exact List.mem_append_left _ (by simpa using member)
            | succ offset =>
                apply List.mem_append_right
                apply ih tail offset actual found child
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member
      next => cases computed

theorem variant_missing_discards_prefix {terms : TermEndpoints} {upper lower : List Alternative}
    {index : Nat} {actual : Alternative} (missing : upper.any (matching actual) = false) :
    variantChildren terms upper index (actual :: lower) = .error index := by
  simp [variantChildren, missing]

theorem variant_first_missing {terms : TermEndpoints} {upper before after : List Alternative}
    {start : Nat} {actual : Alternative}
    (earlier : ∀ candidate ∈ before, upper.any (matching candidate) = true)
    (missing : upper.any (matching actual) = false) :
    variantChildren terms upper start (before ++ actual :: after) = .error (start + before.length) := by
  induction before generalizing start with
  | nil => simp [variantChildren, missing]
  | cons first rest ih =>
      have found := earlier first List.mem_cons_self
      have remaining : ∀ candidate ∈ rest, upper.any (matching candidate) = true :=
        fun candidate member => earlier candidate (List.mem_cons_of_mem _ member)
      simp [variantChildren, found, ih remaining, Except.map, Nat.add_comm, Nat.add_left_comm]

theorem argument_effect_scope {arena : Arena} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {task : Pair} {receipt : Receipt} {demand : ScopedDemand}
    (valid : AdmissionResult arena views qv qe parent post derived
      ⟨.function .argumentEffect, task⟩ receipt)
    (deferred : parent.flow.demand = some demand) :
    genuineDemand parent demand ∧ receipt.child.flow.demand = none ∧
      arena.transformerAt receipt.child.flow.transformer = some (.stamp demand.inputRoute) := by
  simpa only [FlowResult, deferred] using valid.flow_exact.2

theorem result_effect_scope {arena : Arena} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {task : Pair} {receipt : Receipt} {demand : ScopedDemand}
    (valid : AdmissionResult arena views qv qe parent post derived
      ⟨.function .resultEffect, task⟩ receipt)
    (deferred : parent.flow.demand = some demand) :
    genuineDemand parent demand ∧ receipt.child.flow.demand = none ∧
      arena.transformerAt receipt.child.flow.transformer =
        some (.protect demand.outputScope demand.inputRoute) := by
  simpa only [FlowResult, deferred] using valid.flow_exact.2

theorem admission_result_kept {before after : Arena} (extension : before.Extends after)
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {parent : Key}
    {post : Nat} {derived : Bool} {child : Child} {receipt : Receipt}
    (valid : AdmissionResult before views qv qe parent post derived child receipt) :
    AdmissionResult after views qv qe parent post derived child receipt := by
  refine ⟨valid.parent_same, valid.port_same, valid.derived_same, valid.pair_exact,
    valid.sources_same, ?_, flow_result_kept extension valid.flow_exact,
    valid.guards, extension.2.2 _ _ valid.registered⟩
  obtain ⟨weight, found, context⟩ := valid.context_exact
  exact ⟨weight, found, context_result_kept extension context⟩

structure NativeWork where
  task : Pair
  relation : Option Nat
  replayAck : Option (Nat × Nat)
  deriving DecidableEq, Repr

structure Work where
  source : Child
  receipt : Receipt
  deriving DecidableEq, Repr

def Work.native (work : Work) : NativeWork :=
  ⟨work.source.task, some work.receipt.relation, none⟩

/-- `done.length` is the native next cursor. The remaining list is a view of
the immutable children vector in its actual reverse admission order. -/
structure Cursor where
  arena : Arena
  done : List Child := []
  todo : List Child
  pending : Option Receipt := none
  records : List Work := []
  queue : List NativeWork

def initialCursor (arena : Arena) (children : List Child) (queue : List NativeWork) : Cursor :=
  ⟨arena, [], children.reverse, none, [], queue⟩

def Cursor.admitted (cursor : Cursor) (arena : Arena) (receipt : Receipt) : Cursor :=
  {cursor with arena := arena, pending := some receipt}

def Cursor.enqueued (cursor : Cursor) (child : Child) (rest : List Child)
    (receipt : Receipt) : Cursor :=
  {cursor with
    done := cursor.done ++ [child]
    todo := rest
    pending := none
    records := cursor.records ++ [⟨child, receipt⟩]
    queue := Work.native ⟨child, receipt⟩ :: cursor.queue}

inductive DispatchStep (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) : Cursor → Cursor → Prop where
  | admit {cursor : Cursor} {child : Child} {rest : List Child} {arena : Arena} {receipt : Receipt}
      (idle : cursor.pending = none) (next : cursor.todo = child :: rest)
      (computed : NativeValuePorts.admit cursor.arena views qv qe parent post derived child =
        some (arena, receipt)) :
      DispatchStep views qv qe parent post derived cursor (cursor.admitted arena receipt)
  | enqueue {cursor : Cursor} {child : Child} {rest : List Child} {receipt : Receipt}
      (next : cursor.todo = child :: rest) (pending : cursor.pending = some receipt) :
      DispatchStep views qv qe parent post derived cursor (cursor.enqueued child rest receipt)

structure CursorValid (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) (children : List Child)
    (queue : List NativeWork) (cursor : Cursor) : Prop where
  split : cursor.done ++ cursor.todo = children.reverse
  records : cursor.records.map Work.source = cursor.done
  queue_exact : cursor.queue = cursor.records.reverse.map Work.native ++ queue
  checked : ∀ work ∈ cursor.records,
    AdmissionResult cursor.arena views qv qe parent post derived work.source work.receipt
  pending : ∀ receipt, cursor.pending = some receipt →
    ∃ child rest, cursor.todo = child :: rest ∧
      AdmissionResult cursor.arena views qv qe parent post derived child receipt

theorem initial_cursor_valid (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) (children : List Child)
    (queue : List NativeWork) (arena : Arena) :
    CursorValid views qv qe parent post derived children queue (initialCursor arena children queue) := by
  exact ⟨rfl, rfl, rfl, by simp [initialCursor], by simp [initialCursor]⟩

theorem dispatch_step_valid {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {children : List Child}
    {queue : List NativeWork} {before after : Cursor}
    (step : DispatchStep views qv qe parent post derived before after)
    (valid : CursorValid views qv qe parent post derived children queue before) :
    CursorValid views qv qe parent post derived children queue after := by
  cases step with
  | @admit child rest arena receipt idle next computed =>
      have result := admit_constructs computed
      refine ⟨valid.split, valid.records, valid.queue_exact, ?_, ?_⟩
      · intro work member
        exact admission_result_kept result.1 (valid.checked work member)
      · intro other pending
        have equal : receipt = other := Option.some.inj pending
        subst other
        exact ⟨child, rest, next, result.2⟩
  | @enqueue child rest receipt next pending =>
      obtain ⟨actual, remaining, same, checked⟩ := valid.pending receipt pending
      rw [next] at same
      cases same
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [Cursor.enqueued, List.append_assoc, next] using valid.split
      · simp [Cursor.enqueued, valid.records]
      · simp [Cursor.enqueued, valid.queue_exact]
      · intro work member
        simp only [Cursor.enqueued, List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact valid.checked work old
        · exact checked
      · simp [Cursor.enqueued]

inductive DispatchRun (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) : Cursor → Cursor → Prop where
  | refl (cursor : Cursor) : DispatchRun views qv qe parent post derived cursor cursor
  | step {first middle last : Cursor}
      (next : DispatchStep views qv qe parent post derived first middle)
      (rest : DispatchRun views qv qe parent post derived middle last) :
      DispatchRun views qv qe parent post derived first last

theorem dispatch_run_valid {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {children : List Child}
    {queue : List NativeWork} {before after : Cursor}
    (run : DispatchRun views qv qe parent post derived before after)
    (valid : CursorValid views qv qe parent post derived children queue before) :
    CursorValid views qv qe parent post derived children queue after := by
  induction run with
  | refl => exact valid
  | step next rest ih => exact ih (dispatch_step_valid next valid)

theorem next_source_index {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {children : List Child}
    {queue : List NativeWork} {cursor : Cursor} {child : Child} {rest : List Child}
    (valid : CursorValid views qv qe parent post derived children queue cursor)
    (next : cursor.todo = child :: rest) :
    children.reverse[cursor.done.length]? = some child := by
  rw [← valid.split, next, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- The native end-of-vector test entails that no child is still awaiting
enqueue, by the same reachable-state invariant. -/
theorem finished_pending_none {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {children : List Child}
    {queue : List NativeWork} {cursor : Cursor}
    (valid : CursorValid views qv qe parent post derived children queue cursor)
    (finished : cursor.todo = []) : cursor.pending = none := by
  cases pending : cursor.pending with
  | none => rfl
  | some receipt =>
      obtain ⟨child, rest, next, _⟩ := valid.pending receipt pending
      simp [finished] at next

/-- A completed native two-phase scan has exactly the original children in
front-of-queue source order. Every one retains a constructed complete key;
none is inferred merely from an admission bit or a consumed Replay ticket. -/
theorem completed_dispatch_readback {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {children : List Child}
    {queue : List NativeWork} {arena : Arena} {cursor : Cursor}
    (run : DispatchRun views qv qe parent post derived (initialCursor arena children queue) cursor)
    (finished : cursor.todo = []) :
    ∃ jobs : List Work,
      jobs.map Work.source = children ∧
      cursor.queue = jobs.map Work.native ++ queue ∧
      (∀ work ∈ jobs, AdmissionResult cursor.arena views qv qe parent post derived
        work.source work.receipt) ∧
      (∀ work ∈ jobs, work.native.replayAck = none) := by
  have valid := dispatch_run_valid run (initial_cursor_valid _ _ _ _ _ _ _ _ _)
  have done : cursor.done = children.reverse := by simpa [finished] using valid.split
  refine ⟨cursor.records.reverse, ?_, valid.queue_exact, ?_, ?_⟩
  · rw [List.map_reverse, valid.records, done, List.reverse_reverse]
  · intro work member
    exact valid.checked work (List.mem_reverse.mp member)
  · intro work _; rfl

/-- A finite execution of the actual two-stage loop. Fuel is a proof-side
step counter, not a new bound on native accepted programs. -/
def drive (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) : Nat → Cursor → Option Cursor
  | 0, cursor => if cursor.todo = [] then some cursor else none
  | n + 1, cursor =>
      match cursor.todo with
      | [] => some cursor
      | child :: rest =>
          match cursor.pending with
          | none => do
              let (arena, receipt) ← admit cursor.arena views qv qe parent post derived child
              drive views qv qe parent post derived n (cursor.admitted arena receipt)
          | some receipt =>
              drive views qv qe parent post derived n (cursor.enqueued child rest receipt)

theorem drive_constructs_run {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {fuel : Nat} {before after : Cursor}
    (computed : drive views qv qe parent post derived fuel before = some after) :
    DispatchRun views qv qe parent post derived before after ∧ after.todo = [] := by
  induction fuel generalizing before after with
  | zero =>
      unfold drive at computed
      split at computed
      · cases computed; exact ⟨.refl _, ‹before.todo = []›⟩
      · cases computed
  | succ fuel ih =>
      cases next : before.todo with
      | nil =>
          simp only [drive, next, Option.some.injEq] at computed
          subst after
          exact ⟨.refl _, next⟩
      | cons child rest =>
          cases pending : before.pending with
          | none =>
              simp only [drive, next, pending] at computed
              obtain ⟨⟨arena, receipt⟩, admitted, remaining⟩ := Option.bind_eq_some_iff.mp computed
              obtain ⟨run, finished⟩ := ih remaining
              exact ⟨.step (.admit pending next admitted) run, finished⟩
          | some receipt =>
              simp only [drive, next, pending] at computed
              obtain ⟨run, finished⟩ := ih computed
              exact ⟨.step (.enqueue next pending) run, finished⟩

theorem drive_success_readback {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {children : List Child}
    {queue : List NativeWork} {arena : Arena} {fuel : Nat} {cursor : Cursor}
    (computed : drive views qv qe parent post derived fuel
      (initialCursor arena children queue) = some cursor) :
    cursor.pending = none ∧
    ∃ jobs : List Work, jobs.map Work.source = children ∧
      cursor.queue = jobs.map Work.native ++ queue ∧
      (∀ work ∈ jobs, AdmissionResult cursor.arena views qv qe parent post derived
        work.source work.receipt) ∧
      (∀ work ∈ jobs, work.native.replayAck = none) := by
  obtain ⟨run, finished⟩ := drive_constructs_run computed
  exact ⟨finished_pending_none
    (dispatch_run_valid run (initial_cursor_valid _ _ _ _ _ _ _ _ _)) finished,
    completed_dispatch_readback run finished⟩

namespace Witness

def terms : TermEndpoints :=
  ⟨ValueEndpoint.row, ValueEndpoint.row, Endpoint.row, Endpoint.row⟩

def parent : Key :=
  ⟨.value (.positiveFunction 1) (.negativeFunction 2), 1, some 9,
    ⟨0, some ⟨11, 12, 2, 13, 14⟩⟩⟩

def children : List Child := functionChildren terms ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩
def views : Nat → Option (Option Nat) := fun _ => some none

def arena : Arena := ⟨[.without 0], [], [parent]⟩

theorem arena_context_formed : ContextsFormed arena.contexts := by
  intro index node found input member
  cases index with
  | zero => simp [arena] at found; subst node; simpa [contextInputs] using member
  | succ index => simp [arena] at found

def completed : Option Cursor := drive views id id parent 1 true 8 (initialCursor arena children [])

theorem function_drive_returns : completed.isSome = true := by decide

theorem function_drive_whole :
    ∃ cursor, completed = some cursor ∧ cursor.pending = none ∧
      ∃ jobs : List Work, jobs.map Work.source = children ∧
        cursor.queue = jobs.map Work.native ∧
        (∀ work ∈ jobs, AdmissionResult cursor.arena views id id parent 1 true
          work.source work.receipt) ∧
        (∀ work ∈ jobs, work.native.replayAck = none) := by
  cases found : completed with
  | none => have h := function_drive_returns; simp [found] at h
  | some cursor =>
      obtain ⟨pending, jobs, sources, queue, receipts, ack⟩ := drive_success_readback found
      exact ⟨cursor, rfl, pending, jobs, sources, by simpa using queue, receipts, ack⟩

theorem variant_duplicate_requirements :
    variantChildren terms [⟨7, [2]⟩, ⟨7, [3]⟩] 0 [⟨7, [1]⟩] =
      .ok [⟨.variant 0 0 0, .value (.row 1) (.row 2)⟩,
           ⟨.variant 0 1 0, .value (.row 1) (.row 3)⟩] := rfl

theorem record_original_indices :
    recordChildren terms parent [(7, ⟨1, false⟩)]
      [(5, ⟨2, true⟩), (7, ⟨3, false⟩)] =
        .ok [⟨.record 0 1, .value (.row 1) (.row 3)⟩] := rfl

theorem prefixed_argument_context :
    let result := buildContext arena (some 7) 1 true
    result.1.contexts = [.without 0, .prefix 7 0, .swap 1, .prefix 7 3] ∧ result.2 = 4 := by decide

end Witness

end YulangClosure.NativeValuePorts
