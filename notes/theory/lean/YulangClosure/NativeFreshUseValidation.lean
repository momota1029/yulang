import YulangClosure.NativeFreshScopeTransport
import YulangClosure.Contracts

/-!
Research-only, constructor-directed native FreshUse observation. The two
recursions below read different tables: `interpret` reads the immutable captured
graph and `observe` reads native term handles. Neither reads retained terms.
`Payload` means an ENTIRE immutable native payload, with its original identities;
its extraction is a source-authentication obligation, not a semantic quotient.
Fuel exhaustion, absent entries, malformed slices and unsupported certificates
produce `none`, never successful validation. No assertion here states that every
successful Rust reconstruction validates, or identifies this model with source
typing. Original InferenceSoundness and effect hygiene remain open.

INCOMPLETE SOURCE CORRESPONDENCE: the abstract Payload below has not been
instantiated for native Contribution.instance, View.source_weight/closed_weight,
or remapped Context weight/view handles. The Context recipe currently observes
its supplied context; it does not construct native weight remapping. No theorem
in this file establishes validation of those concrete Rust fields, complete-map
coverage, or native handle equality. This file is constructed but UNCHECKED;
the primary alone owns Lean execution and axiom auditing.
-/
namespace YulangClosure.NativeFreshUseValidation

inductive Polarity where
  | positive | negative
  deriving DecidableEq, Repr

inductive RowKey where
  | value (ordinal : Nat) | effect (ordinal : Nat)
  deriving DecidableEq, Repr

inductive Atom where
  | bottom | top | negativeBottom
  | intPositive | intNegative | unitPositive | boolPositive | strPositive
  | unitNegative | boolNegative | strNegative | effectBottom | emptyEffect
  deriving DecidableEq, Repr

structure Field (α : Type) where
  name : String
  optional : Bool
  value : α
  deriving DecidableEq, Repr

structure Alternative (α : Type) where
  tag : String
  payloads : List α
  deriving DecidableEq, Repr

/-- Source endpoint IDs; the four freshenable native forms are distinct. -/
inductive Endpoint where
  | contribution (id : Nat)
  | allowance (id : Nat)
  | support (id : Nat)
  | annotationMember (id member : Nat)
  | bottomPositive | emptyNegative | effectRow (row : Nat)
  deriving DecidableEq, Repr

inductive Operand (Payload : Type) where
  | contribution (payload : Payload)
  | allowance (payload : Payload) (tail : Option RowKey)
  | support (payload : Payload) (tail : Option RowKey)
  | annotationMember (payload : Payload) (tail : Option RowKey) (member : Nat)
  deriving DecidableEq, Repr

inductive Label (Payload : Type) where
  | atom (atom : Atom)
  | row (polarity : Polarity) (key : RowKey)
  | function (polarity : Polarity)
  | tuple (polarity : Polarity)
  | record (polarity : Polarity)
  | field (name : String) (optional : Bool)
  | variant (polarity : Polarity)
  | alternative (tag : String)
  | operand (polarity : Polarity) (value : Operand Payload)
  | mapEntry (kind key : Nat)
  | number (value : Nat)
  | payload (value : Payload)
  | transformer (value : NativeScopeTransformer.Transformer)
  | context (constructor : Nat)
  deriving DecidableEq, Repr

inductive Tree (Payload : Type) where
  | node (label : Label Payload) (children : List (Tree Payload))
  deriving DecidableEq, Repr

/-- Both decoders expose all structural content, including optional presence. -/
inductive View (α Payload : Type) where
  | leaf (atom : Atom)
  | operand (polarity : Polarity) (value : Operand Payload)
  | row (polarity : Polarity) (key : RowKey)
  | function (polarity : Polarity) (argument argumentEffect resultEffect result : α)
  | tuple (polarity : Polarity) (children : List α)
  | record (polarity : Polarity) (fields : List (Field α))
  | variant (polarity : Polarity) (alternatives : List (Alternative α))

def sequence {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | head :: rest => do
      let first ← f head
      let others ← sequence f rest
      pure (first :: others)

def expand {α Payload : Type} (child : α → Option (Tree Payload)) :
    View α Payload → Option (Tree Payload)
  | .leaf atom => some (.node (.atom atom) [])
  | .operand polarity value => some (.node (.operand polarity value) [])
  | .row polarity key => some (.node (.row polarity key) [])
  | .function polarity a ae re r => do
      let a' ← child a
      let ae' ← child ae
      let re' ← child re
      let r' ← child r
      pure (.node (.function polarity) [a', ae', re', r'])
  | .tuple polarity children => do
      let children' ← sequence child children
      pure (.node (.tuple polarity) children')
  | .record polarity fields => do
      let fields' ← sequence (fun field => do
        let value ← child field.value
        pure (.node (.field field.name field.optional) [value])) fields
      pure (.node (.record polarity) fields')
  | .variant polarity alternatives => do
      let alternatives' ← sequence (fun alternative => do
        let values ← sequence child alternative.payloads
        pure (.node (.alternative alternative.tag) values)) alternatives
      pure (.node (.variant polarity) alternatives')

inductive Node where
  | leaf (atom : Atom)
  | effectOperand (endpoint : Endpoint) (tail : Option Nat) (polarity : Polarity)
  | row (row : Nat) (polarity : Polarity)
  | function (polarity : Polarity) (argument argumentEffect resultEffect result : Nat)
  | tuple (polarity : Polarity) (start length : Nat)
  | record (polarity : Polarity) (start length : Nat)
  | variant (polarity : Polarity) (start length : Nat)

structure Graph where
  nodes : List Node
  tupleChildren : List Nat
  recordFields : List (Field Nat)
  variantAlternatives : List (Alternative Nat)
  root : Nat

def slice {α : Type} (items : List α) (start length : Nat) : Option (List α) :=
  if start + length ≤ items.length then some ((items.drop start).take length) else none

/-- Independently captured whole view/contribution payloads. View tails are
replaced from the SAME row vector, not retained effect-operand entries. -/
structure Snapshot (Payload : Type) where
  views : Nat → Option Payload
  contributions : Nat → Option Payload

def tailRow (graph : Graph) (rows : List RowKey) : Option Nat → Option (Option RowKey)
  | none => some none
  | some index => do
      match ← graph.nodes[index]? with
      | .row row _ =>
          match ← rows[row]? with
          | .effect key => pure (some (.effect key))
          | .value _ => none
      | _ => none

def operand (snapshot : Snapshot Payload) (endpoint : Endpoint)
    (tail : Option RowKey) : Option (Operand Payload) :=
  match endpoint with
  | .contribution id => Operand.contribution <$> snapshot.contributions id
  | .allowance id => (fun value => Operand.allowance value tail) <$> snapshot.views id
  | .support id => (fun value => Operand.support value tail) <$> snapshot.views id
  | .annotationMember id member =>
      (fun value => Operand.annotationMember value tail member) <$> snapshot.views id
  | .bottomPositive | .emptyNegative | .effectRow _ => none

def graphView (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (index : Nat) : Option (View Nat Payload) := do
  match ← graph.nodes[index]? with
  | .leaf atom => pure (.leaf atom)
  | .effectOperand endpoint tail polarity => do
      let tail' ← tailRow graph rows tail
      let value ← operand snapshot endpoint tail'
      pure (.operand polarity value)
  | .row row polarity => do
      let key ← rows[row]?
      pure (.row polarity key)
  | .function polarity a ae re r => pure (.function polarity a ae re r)
  | .tuple polarity start length => do
      let children ← slice graph.tupleChildren start length
      pure (.tuple polarity children)
  | .record polarity start length => do
      let fields ← slice graph.recordFields start length
      pure (.record polarity fields)
  | .variant polarity start length => do
      let alternatives ← slice graph.variantAlternatives start length
      pure (.variant polarity alternatives)

def unfoldView (read : Nat → Option (View Nat Payload)) : Nat → Nat → Option (Tree Payload)
  | 0, _ => none
  | fuel + 1, index => do
      let view ← read index
      expand (unfoldView read fuel) view

def interpret (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (fuel index : Nat) : Option (Tree Payload) :=
  unfoldView (graphView graph rows snapshot) fuel index

/-- The native reader must read actual interner handles. In particular a native
row is a LiveVariable of its exact kind/ordinal/polarity; collected Component
handles have no admitted decoder in this reconstruction. -/
def observe (nativeRead : Nat → Option (View Nat Payload))
    (fuel term : Nat) : Option (Tree Payload) := unfoldView nativeRead fuel term

structure Demand where
  originalCall : Nat
  useInstance : Nat
  rootNode : Nat
  outputScope : Nat
  input : Nat

/-- All native ContextExpr forms. BothFromRight is represented but rejected:
the pinned native fresh-context constructor rejects its certificate. -/
inductive Context (Payload : Type) where
  | identity
  | prefix (weight : Payload) (input : Context Payload)
  | suffix (input : Context Payload) (weight : Payload)
  | swap (input : Context Payload)
  | bothFromRight (input : Context Payload) (certificate : Nat)
  | replay (lower upper : Context Payload)
  | withoutLeftFilter (input : Context Payload)

def contextTree : Context Payload → Option (Tree Payload)
  | .identity => some (.node (.context 0) [])
  | .prefix weight input => do
      let input' ← contextTree input
      pure (.node (.context 1) [.node (.payload weight) [], input'])
  | .suffix input weight => do
      let input' ← contextTree input
      pure (.node (.context 2) [input', .node (.payload weight) []])
  | .swap input => do
      let input' ← contextTree input
      pure (.node (.context 3) [input'])
  | .bothFromRight _ _ => none
  | .replay lower upper => do
      let lower' ← contextTree lower
      let upper' ← contextTree upper
      pure (.node (.context 5) [lower', upper'])
  | .withoutLeftFilter input => do
      let input' ← contextTree input
      pure (.node (.context 6) [input'])

/-- Map recipes carry captured source CONTENT, not a desired mapped result.
Context weight-payload extraction/remapped view tails remain explicit source
authentication duties; an unresolved recipe always prevents success. -/
inductive MapRecipe (Payload : Type) where
  | region (old : Nat)
  | scope (old : Nat)
  | input (old : Nat)
  | contextUse
  | scopedRelation (relation : Nat) (transformer : NativeScopeTransformer.Transformer)
      (demand : Option Demand)
  | attachmentBundle (old : Nat) (wholePayload : Payload)
  | context (old : Nat) (source : Context Payload)
  | evidence (index : Nat) (wholeSnapshot : Payload)
  | roleObligation (index row : Nat)
  | fieldObligation (index receiver receiverEffect result resultEffect : Nat)
  | unresolved (field : String)

structure Allocation where
  regionCount : Nat
  regionKeys : List Nat
  scopeCount : Nat
  scopeKeys : List Nat
  inputCount : Nat
  inputKeys : List Nat
  contextUse : Nat

def Allocation.regions (allocation : Allocation) : Nat → Nat :=
  (NativeFreshScopeTransport.fresh allocation.regionCount allocation.regionKeys).remap
def Allocation.scopes (allocation : Allocation) : Nat → Nat :=
  (NativeFreshScopeTransport.fresh allocation.scopeCount allocation.scopeKeys).remap
def Allocation.inputs (allocation : Allocation) : Nat → Nat :=
  (NativeFreshScopeTransport.fresh allocation.inputCount allocation.inputKeys).remap

def numbers (values : List Nat) : List (Tree Payload) :=
  values.map (fun value => .node (.number value) [])

def interpretMap (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (fuel : Nat) (allocation : Allocation) : MapRecipe Payload → Option (Tree Payload)
  | .region old => some (.node (.mapEntry 0 old) (numbers [allocation.regions old]))
  | .scope old => some (.node (.mapEntry 1 old) (numbers [allocation.scopes old]))
  | .input old => some (.node (.mapEntry 2 old) (numbers [allocation.inputs old]))
  | .contextUse => some (.node (.mapEntry 3 0) (numbers [allocation.contextUse]))
  | .scopedRelation relation transformer demand => do
      let demand' ← match demand with
        | none => some []
        | some demand => do
            let root ← interpret graph rows snapshot fuel demand.rootNode
            let use := if demand.input ∈ allocation.inputKeys then
              allocation.contextUse else demand.useInstance
            pure (numbers [demand.originalCall, use,
              allocation.scopes demand.outputScope, allocation.inputs demand.input] ++ [root])
      pure (.node (.mapEntry 4 relation)
        (.node (.transformer (transformer.rename allocation.scopes allocation.inputs)) [] :: demand'))
  | .attachmentBundle old payload => some (.node (.mapEntry 5 old) [.node (.payload payload) []])
  | .context old source => do
      let context ← contextTree source
      pure (.node (.mapEntry 6 old) [context])
  | .evidence index payload => some (.node (.mapEntry 7 index) [.node (.payload payload) []])
  | .roleObligation index row => do
      let key ← rows[row]?
      pure (.node (.mapEntry 8 index) [.node (.row .positive key) []])
  | .fieldObligation index receiver receiverEffect result resultEffect => do
      let receiver' ← rows[receiver]?
      let receiverEffect' ← rows[receiverEffect]?
      let result' ← rows[result]?
      let resultEffect' ← rows[resultEffect]?
      pure (.node (.mapEntry 9 index)
        ([receiver', receiverEffect', result', resultEffect'].map
          (fun key => .node (.row .positive key) [])))
  | .unresolved _ => none

/-- Compare only successful independent observations. `none = none` does NOT
validate. This is also used for the dependent map observations. -/
def validateObservation [DecidableEq Payload]
    (expected actual : Option (Tree Payload)) : Bool :=
  match expected, actual with
  | some one, some two => decide (one = two)
  | _, _ => false

theorem validateObservation_sound [DecidableEq Payload]
    {expected actual : Option (Tree Payload)}
    (valid : validateObservation expected actual = true) :
    ∃ value, expected = some value ∧ actual = some value := by
  cases expected with
  | none => simp [validateObservation] at valid
  | some one =>
      cases actual with
      | none => simp [validateObservation] at valid
      | some two =>
          have same : one = two := of_decide_eq_true valid
          exact ⟨one, rfl, congrArg some same.symm⟩

def validateNode [DecidableEq Payload] (graph : Graph) (rows : List RowKey)
    (snapshot : Snapshot Payload) (nativeRead : Nat → Option (View Nat Payload))
    (fuel index : Nat) (term : Option Nat) (effectRead : Nat → Option (Tree Payload)) : Bool :=
  match graph.nodes[index]? with
  | some (.effectOperand _ _ _) =>
      term.isNone && validateObservation (interpret graph rows snapshot fuel index) (effectRead index)
  | some _ => match term with
      | none => false
      | some term => validateObservation (interpret graph rows snapshot fuel index)
          (observe nativeRead fuel term)
  | none => false

/-- Ordinary root theorem, covering Leaf/Row/Function/Tuple/Record/Variant,
without any assumed root image equation. Effect operands use their own map. -/
theorem validateNode_term_sound [DecidableEq Payload]
    (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (nativeRead : Nat → Option (View Nat Payload)) (fuel index term : Nat)
    (effectRead : Nat → Option (Tree Payload))
    (valid : validateNode graph rows snapshot nativeRead fuel index (some term) effectRead = true) :
    ∃ value, interpret graph rows snapshot fuel index = some value ∧
      observe nativeRead fuel term = some value := by
  unfold validateNode at valid
  cases node : graph.nodes[index]? with
  | none => simp [node] at valid
  | some node =>
      cases node <;> simp only [node] at valid
      all_goals first
        | exact validateObservation_sound valid
        | simp at valid

theorem validateNode_effect_sound [DecidableEq Payload]
    (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (nativeRead : Nat → Option (View Nat Payload)) (fuel index : Nat)
    (effectRead : Nat → Option (Tree Payload))
    (isEffect : ∃ endpoint tail polarity,
      graph.nodes[index]? = some (.effectOperand endpoint tail polarity))
    (valid : validateNode graph rows snapshot nativeRead fuel index none effectRead = true) :
    ∃ value, interpret graph rows snapshot fuel index = some value ∧
      effectRead index = some value := by
  obtain ⟨endpoint, tail, polarity, atIndex⟩ := isEffect
  exact validateObservation_sound (by simpa [validateNode, atIndex] using valid)

theorem validateMap_sound [DecidableEq Payload]
    (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (fuel : Nat) (allocation : Allocation) (recipe : MapRecipe Payload)
    (actual : Option (Tree Payload))
    (valid : validateObservation (interpretMap graph rows snapshot fuel allocation recipe) actual = true) :
    ∃ value, interpretMap graph rows snapshot fuel allocation recipe = some value ∧
      actual = some value := validateObservation_sound valid

/-- The constructor is present in the model, but never silently admitted. -/
theorem unresolved_map_rejected [DecidableEq Payload]
    (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (fuel : Nat) (allocation : Allocation) (field : String)
    (actual : Option (Tree Payload)) :
    validateObservation (interpretMap graph rows snapshot fuel allocation (.unresolved field)) actual = false := by
  cases actual <;> rfl

/-- Apply the validated root to the ACTUAL returned handle. The hypothesis is
only the native return-site identification, not the desired interpretation. -/
theorem returned_root_observation [DecidableEq Payload]
    (graph : Graph) (rows : List RowKey) (snapshot : Snapshot Payload)
    (nativeRead : Nat → Option (View Nat Payload)) (fuel returned : Nat)
    (retained : Nat → Option Nat) (effectRead : Nat → Option (Tree Payload))
    (returnSite : retained graph.root = some returned)
    (valid : validateNode graph rows snapshot nativeRead fuel graph.root
      (retained graph.root) effectRead = true) :
    ∃ value, interpret graph rows snapshot fuel graph.root = some value ∧
      observe nativeRead fuel returned = some value := by
  rw [returnSite] at valid
  exact validateNode_term_sound graph rows snapshot nativeRead fuel graph.root returned effectRead valid

end YulangClosure.NativeFreshUseValidation
