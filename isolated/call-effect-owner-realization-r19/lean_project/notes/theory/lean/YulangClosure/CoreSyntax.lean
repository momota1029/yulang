import Init

namespace YulangClosure.Original

inductive Space where
  | value | type | evidence | control
  deriving DecidableEq

inductive Base where
  | unit | bool | int | float | string | bytes | path | char
  deriving DecidableEq

inductive Literal where
  | unit
  | bool (value : Bool)
  | int (value : Int)
  | floatBits (bits : UInt64)
  | string (value : String)
  | bytes (value : List UInt8)
  | path (value : List UInt8)
  | char (value : String)

inductive Mode where | value | computation
  deriving DecidableEq
inductive EvidenceMode where | general | administrative
inductive Failure where | matchFailure | divideByZero | boundsError | unimplemented
inductive IdentityKind where
  | nominal | constructor | operation | family | resource | stateScope
  | owner | handler | graphRoot | template | primitive | label | receipt | view | target

/-- Identity atoms are NOT variables and are never rewritten by substitution. -/
inductive Atom where
  | literal (value : Literal)
  | identity (kind : IdentityKind) (key : Nat)
  | mode (entryMode : Mode)
  | evidenceMode (value : EvidenceMode)
  | failure (value : Failure)
  | presence (required : Bool)
  | base (value : Base)
  | index (value : Nat)

/-- Named original constructors, not a body-opcode interpreter. Their arities
and sort constraints are extrinsic. All arguments, including metadata and type
instances, remain children of the raw tree. -/
inductive Tag where
  | typeTop | typeBottom | typeUnion | typeIntersection | typeTuple | typeRecord
  | typeVariant | typeNominal | typeMu | typeThunk | typeCallable | typeAll
  | typeContinuation | typeEvidence
  | tuple | sequence | record | variant | nominal | lambda | delay | wrap
  | typeAbstract | typeApply | inject | both | roll | top | valueView | continuation
  | evidenceAbstract | graphReference
  | ret | bind | force | call | resume | split | field | lookup | switch | unroll
  | choose | unionCase | absurd | primitive | perform | handle | mapop | recBlock
  | template | fail | bad | evidenceApply | release
  | scope | expose | enter | tryArm | waitArm | request | operationInstance
  | handlerDeclaration | valueArm | operationArm | mapper | directEvidence
  | adminEffect | adminResult | fieldDeclaration | variantDeclaration

mutual
  inductive Raw where
    | var (space : Space) (index : Nat)
    | atom (atom : Atom)
    | node (tag : Tag) (children : Forest)
    | bind (space : Space) (body : Raw)
  inductive Forest where
    | nil
    | cons (head : Raw) (tail : Forest)
end

def Forest.one (x : Raw) : Forest := .cons x .nil
def Forest.two (x y : Raw) : Forest := .cons x (.cons y .nil)

def rawLet (m n : Raw) : Raw := .node .bind (.two m (.bind .value n))
def rawDelay (m : Raw) : Raw := .node .delay (.one m)
def rawRet (v : Raw) : Raw := .node .ret (.one v)
def rawForce (v : Raw) : Raw := .node .force (.one v)

/-- One stored underlying value. The two evidence children are derivations/views
of THIS child, not two independent values. The typing rule must enforce this. -/
def rawBoth (v leftEvidence rightEvidence : Raw) : Raw :=
  .node .both (.cons v (.two leftEvidence rightEvidence))

/-- Payload and response reference one shared operation-instance child. -/
def rawOperationInstance (operation : Nat) (typeArguments : Forest) : Raw :=
  .node .operationInstance (.cons (.atom (.identity .operation operation)) typeArguments)

/-! Explicit binder convention:
let/lambda/continuation: one value binder; eabs: one evidence binder.
The source eabs formal is a term-level dictionary value. A future lexical
encoding must map occurrences resolved to that formal to evidence index0,
shift only for nested evidence binders, and preserve separately resolved value
locals. Eapp must substitute its argument in that evidence namespace. This
encoding/typing is not yet defined or used by the proved fragment.

All/typeAbstract/mu: one type binder; split and recBlock: nested value binders
in declaration order, with ALL recursive RHSs beneath the same binder block.
Polymorphic arms put their rigid type binders outside the paired instance,
payload and continuation formal binders. Control binders are separate; existing
immutable identity atoms are not in that substitution namespace.
Malformed arity, mismatched namespace and invalid evidence are representable.
Full constructor well-formedness/typing is not claimed by this raw grammar. -/

/-- Explicit original fragment for the first extrinsic substitution proof.
It embeds below into Raw. Other raw constructors remain present and OPEN. -/
inductive Ty where
  | base (kind : Base)
  | thunk (result : Ty)
  | union (left right : Ty)
  | intersection (left right : Ty)
  | top | bottom

mutual
  inductive Val where
    | var (index : Nat)
    | unit
    | bool (value : Bool)
    | int (value : Int)
    | floatBits (value : UInt64)
    | string (value : String)
    | bytes (value : List UInt8)
    | path (value : List UInt8)
    | char (value : String)
    | delay (body : Comp)
    | inLeft (value : Val)
    | inRight (value : Val)
    | both (value : Val)
    | top (value : Val)
  inductive Comp where
    | ret (value : Val)
    | force (value : Val)
    | bind (first body : Comp)
    | unionCase (value : Val) (left right : Comp)
    | chooseLeft (value : Val)
    | chooseRight (value : Val)
    | absurd (value : Val)
end

/-- The base and value representation preserve the existing literal domains. -/
def Literal.base : Literal → Base
  | .unit => .unit
  | .bool _ => .bool
  | .int _ => .int
  | .floatBits _ => .float
  | .string _ => .string
  | .bytes _ => .bytes
  | .path _ => .path
  | .char _ => .char

def Literal.toVal : Literal → Val
  | .unit => .unit
  | .bool v => .bool v
  | .int v => .int v
  | .floatBits v => .floatBits v
  | .string v => .string v
  | .bytes v => .bytes v
  | .path v => .path v
  | .char v => .char v

/-- This computational image erases ONLY the two Prop typing derivations.
The single underlying child is retained; no runtime View/receipt is erased.
Full rawBoth with explicit evidence remains available outside this fragment. -/
def rawProofBoth (v : Raw) : Raw := .node .both (.one v)
def rawTop (v : Raw) : Raw := .node .top (.one v)
def rawIn (right : Bool) (v : Raw) : Raw :=
  .node .inject (.two (.atom (.presence right)) v)
def rawChoose (right : Bool) (v : Raw) : Raw :=
  .node .choose (.two (.atom (.presence right)) v)
def rawUnionCase (v l r : Raw) : Raw :=
  .node .unionCase (.cons v (.two (.bind .value l) (.bind .value r)))
def rawAbsurd (v : Raw) : Raw := .node .absurd (.one v)

mutual
  def Val.raw : Val → Raw
    | .var i => .var .value i
    | .unit => .atom (.literal .unit)
    | .bool v => .atom (.literal (.bool v))
    | .int v => .atom (.literal (.int v))
    | .floatBits v => .atom (.literal (.floatBits v))
    | .string v => .atom (.literal (.string v))
    | .bytes v => .atom (.literal (.bytes v))
    | .path v => .atom (.literal (.path v))
    | .char v => .atom (.literal (.char v))
    | .delay m => rawDelay m.raw
    | .inLeft v => rawIn false v.raw
    | .inRight v => rawIn true v.raw
    | .both v => rawProofBoth v.raw
    | .top v => rawTop v.raw
  def Comp.raw : Comp → Raw
    | .ret v => rawRet v.raw
    | .force v => rawForce v.raw
    | .bind m n => rawLet m.raw n.raw
    | .unionCase v l r => rawUnionCase v.raw l.raw r.raw
    | .chooseLeft v => rawChoose false v.raw
    | .chooseRight v => rawChoose true v.raw
    | .absurd v => rawAbsurd v.raw
end

abbrev Context := Nat → Option Ty

def emptyContext : Context := fun _ => none

def extend (env : Context) (a : Ty) : Context
  | 0 => some a
  | n+1 => env n

mutual
  inductive ValTyped : Context → Val → Ty → Prop
    | var : env i = some a → ValTyped env (.var i) a
    | unit : ValTyped env .unit (.base .unit)
    | bool : ValTyped env (.bool v) (.base .bool)
    | int : ValTyped env (.int v) (.base .int)
    | floatBits : ValTyped env (.floatBits v) (.base .float)
    | string : ValTyped env (.string v) (.base .string)
    | bytes : ValTyped env (.bytes v) (.base .bytes)
    | path : ValTyped env (.path v) (.base .path)
    | char : ValTyped env (.char v) (.base .char)
    | delay : CompTyped env m a → ValTyped env (.delay m) (.thunk a)
    | inLeft : ValTyped env v a → ValTyped env (.inLeft v) (.union a b)
    | inRight : ValTyped env v b → ValTyped env (.inRight v) (.union a b)
    | both : ValTyped env v a → ValTyped env v b →
        ValTyped env (.both v) (.intersection a b)
    | top : ValTyped env v a → ValTyped env (.top v) .top
  inductive CompTyped : Context → Comp → Ty → Prop
    | ret : ValTyped env v a → CompTyped env (.ret v) a
    | force : ValTyped env v (.thunk a) → CompTyped env (.force v) a
    | bind : CompTyped env m a → CompTyped (extend env a) n b →
        CompTyped env (.bind m n) b
    | unionCase : ValTyped env v (.union a b) →
        CompTyped (extend env a) l c → CompTyped (extend env b) r c →
        CompTyped env (.unionCase v l r) c
    | chooseLeft : ValTyped env v (.intersection a b) → CompTyped env (.chooseLeft v) a
    | chooseRight : ValTyped env v (.intersection a b) → CompTyped env (.chooseRight v) b
    | absurd : ValTyped env v .bottom → CompTyped env (.absurd v) a
end

end YulangClosure.Original

/-! A source-derived typed Call fragment.  This is deliberately separate from
`Original.Comp`: the older public fragment has no callable, wrap, request or
failure constructors.  Bodies and adapters below retain their real
`Original.CompTyped` derivations instead of being opaque code labels. -/
namespace YulangClosure.TypedCall

open YulangClosure.Original

inductive CallType where
  | callable (argument result : Original.Ty)
  | thunk (result : Original.Ty)

inductive PortKind where
  | carrier | callEffect | result
  deriving DecidableEq

/-- A source path is a sequence of structural component labels followed by a
typed semantic port. -/
structure PortPath where
  components : List Nat
  port : PortKind
  type : Original.Ty

structure ViewOccurrence where
  identity : Nat
  path : PortPath

inductive PathRule : PortPath → PortPath → Prop where
  | identity (p : PortPath) : PathRule p p
  | prefix (label : Nat) (p q : PortPath) :
      PathRule p q → PathRule ⟨label :: p.components, p.port, p.type⟩
        ⟨label :: q.components, q.port, q.type⟩
  | adapterMap (mappingIdentity : Nat) (p q : PortPath) : PathRule p q

/-- Correspondence is explicit source-plan data.  Equal endpoint types alone
do not create a correspondence edge. -/
structure PathCorrespondence where
  source : PortPath
  target : PortPath
  rule : PathRule source target

structure OperationInstance where
  operation : Nat
  typeArguments : List Original.Ty
  payloadType : Original.Ty
  responseType : Original.Ty

/-! Call values/computations use a separate finite syntax so delayed adapters
remain values even when their code can request or fail. Closed Original values
are embedded explicitly; lexical Call binders use this fragment's variables. -/
mutual
  inductive Value where
    | var (index : Nat)
    | original (value : Original.Val)
    | delay (body : Comp)
    | view (value : Value) (occurrence : ViewOccurrence)
  inductive Comp where
    | original (body : Original.Comp)
    | ret (value : Value)
    | bind (first body : Comp)
    | force (value : Value)
    | scope (owner : Nat) (body : Comp)
    | expose (effectView resultView : ViewOccurrence) (body : Comp)
    | request (opInstance : OperationInstance) (payload : Value)
        (savedContinuation : Comp)
    | fail (reason : Original.Failure)
end

mutual
  inductive ValueTyped : Original.Context → Value → Original.Ty → Prop where
    | var : env index = some type → ValueTyped env (.var index) type
    | original : Original.ValTyped Original.emptyContext value type →
        ValueTyped env (.original value) type
    | delay : CompTyped env body result →
        ValueTyped env (.delay body) (.thunk result)
    | view : ValueTyped env value type →
        ValueTyped env (.view value occurrence) type

  inductive CompTyped : Original.Context → Comp → Original.Ty → Prop where
    | original : Original.CompTyped Original.emptyContext body result →
        CompTyped env (.original body) result
    | ret : ValueTyped env value result → CompTyped env (.ret value) result
    | bind : CompTyped env first a → CompTyped (Original.extend env a) body result →
        CompTyped env (.bind first body) result
    | force : ValueTyped env value (.thunk result) →
        CompTyped env (.force value) result
    | scope : CompTyped env body result → CompTyped env (.scope owner body) result
    | expose (effectView resultView : ViewOccurrence) : CompTyped env body result →
        CompTyped env (.expose effectView resultView body) result
    | request : ValueTyped env payload opInstance.payloadType →
        CompTyped (Original.extend env opInstance.responseType) savedContinuation result →
        CompTyped env (.request opInstance payload savedContinuation) result
    | fail : CompTyped env (.fail reason) result
end

inductive ContextFrame where
  | bind (body : Comp)
  | scope (owner : Nat)
  | expose (effectView resultView : ViewOccurrence)
  | adapter (input output : Original.Ty) (body : Comp)

inductive ContextTyping : Original.Context → List ContextFrame →
    Original.Ty → Original.Ty → Prop where
  | nil : ContextTyping env [] a a
  | bind : CompTyped (Original.extend env a) body b →
      ContextTyping env frames b result →
      ContextTyping env (.bind body :: frames) a result
  | scope : ContextTyping env frames a result →
      ContextTyping env (.scope owner :: frames) a result
  | expose (effectView resultView : ViewOccurrence) :
      ContextTyping env frames a result →
      ContextTyping env (.expose effectView resultView :: frames) a result
  | adapter (hbody : CompTyped (Original.extend env a) body b) :
      ContextTyping env frames b result →
      ContextTyping env (.adapter a b body :: frames) a result

structure ReceiptSlot where
  slot : Nat
  path : PortPath

structure ReceiptTemplate where
  profile : List PortPath
  designatedSlots : List ReceiptSlot

structure InterfacePorts where
  interface : Nat
  callEffect : PortPath
  result : PortPath
  callEffectView : ViewOccurrence
  resultView : ViewOccurrence

/-- The metadata plan for one concrete wrap node.  Keeping the adapters beside
their interface prevents a parallel interface list from drifting away from
the source wrap spine. -/
structure Adapter where
  input : Original.Ty
  output : Original.Ty
  body : Comp
  typed : CompTyped (Original.extend Original.emptyContext input) body output
  pathCorrespondences : List PathCorrespondence
  capturedViews : List ViewOccurrence

structure InterfacePlan where
  ports : InterfacePorts
  argumentAdapter : Adapter
  resultAdapter : Adapter

/-- One source lambda leaf or a finite outer-to-inner wrap spine. -/
inductive Function where
  | lambda (mode : Original.Mode) (receipt : ReceiptTemplate)
      (argument bodyResult result : Original.Ty) (body : Comp)
      (resultConsumer : Adapter) : Function
  | wrap (inner : Function) (argumentAdapter resultAdapter : Adapter) : Function

inductive FunctionTyped : Function → Original.Ty → Original.Ty → Prop where
  | lambdaValue (receipt : ReceiptTemplate) (a bodyResult result : Original.Ty)
      (body : Comp) (resultConsumer : Adapter)
      (h : CompTyped
        (Original.extend Original.emptyContext a) body bodyResult)
      (hc : resultConsumer.input = bodyResult) (hr : resultConsumer.output = result) :
      FunctionTyped (.lambda .value receipt a bodyResult result body resultConsumer) a result
  | lambdaComputation (receipt : ReceiptTemplate) (a bodyResult result : Original.Ty)
      (body : Comp) (resultConsumer : Adapter)
      (h : CompTyped
        (Original.extend Original.emptyContext (.thunk a)) body bodyResult)
      (hc : resultConsumer.input = bodyResult) (hr : resultConsumer.output = result) :
      FunctionTyped (.lambda .computation receipt a bodyResult result body resultConsumer) a result
  | wrap {f : Function} {argumentAdapter resultAdapter : Adapter}
      {a b c d : Original.Ty}
      (hf : FunctionTyped f a b)
      (ha : argumentAdapter.input = c) (haOut : argumentAdapter.output = a)
      (hr : resultAdapter.input = b) (hrOut : resultAdapter.output = d) :
      FunctionTyped (.wrap f argumentAdapter resultAdapter) c d

/-- Immutable source projections used to tie Call metadata to the actual
function syntax. -/
def Function.sourceReceipt : Function → ReceiptTemplate
  | .lambda _ receipt _ _ _ _ _ => receipt
  | .wrap inner _ _ => sourceReceipt inner

def Function.wrapAdapters : Function → List (Adapter × Adapter)
  | .lambda _ _ _ _ _ _ _ => []
  | .wrap inner argumentAdapter resultAdapter =>
      (argumentAdapter, resultAdapter) :: wrapAdapters inner

/-- The receipt, owner, carrier paths, interface ports, adapter path maps and
captured views are frozen inputs to a Call execution. -/
structure CallView where
  receiverOwner : Nat
  sourceReceipt : ReceiptTemplate
  carrierOccurrences : List ViewOccurrence
  interfaces : List InterfacePlan
  adapterPaths : List PathCorrespondence
  capturedViews : List ViewOccurrence

structure Carrier where
  underlying : Value
  carrierType : Original.Ty
  typed : ValueTyped Original.emptyContext underlying carrierType
  occurrences : List ViewOccurrence
  receipts : List ReceiptSlot

/-- A represented source Call has one already selected receiver owner.  The
freshness premise is explicit input data and is not inferred from type equality. -/
structure CallTerm where
  function : Function
  argument : Carrier
  inputType : Original.Ty
  resultType : Original.Ty
  functionTyped : FunctionTyped function inputType resultType
  argumentIsThunk : argument.carrierType = .thunk inputType
  callView : CallView
  sourceReceiptMatches : function.sourceReceipt = callView.sourceReceipt
  wrapPlanMatches : function.wrapAdapters =
    callView.interfaces.map fun plan => (plan.argumentAdapter, plan.resultAdapter)
  activeOwners : List Nat
  receiverFresh : callView.receiverOwner ∉ activeOwners

inductive AdaptersTyped : List Adapter → Original.Ty → Original.Ty → Prop where
  | nil (a : Original.Ty) : AdaptersTyped [] a a
  | cons (adapter : Adapter) (rest : List Adapter)
      (first last middle : Original.Ty)
      (hAdapter : adapter.input = first) (hOutput : adapter.output = middle)
      (hRest : AdaptersTyped rest middle last) :
      AdaptersTyped (adapter :: rest) first last

/-- Typed Call zipper data.  `literalSuffix` is opaque here so the same source
context composes with the actual independently typed Control suffix without
rewriting or inspecting its constructors. -/
structure EvaluationContext (Suffix : Type) where
  activeHole : Comp
  holeType : Original.Ty
  holeTyped : CompTyped Original.emptyContext activeHole holeType
  frames : List ContextFrame
  contextResultType : Original.Ty
  contextTyped : ContextTyping Original.emptyContext frames holeType contextResultType
  pendingDelayedArguments : List Adapter
  pendingArgumentInput : Original.Ty
  pendingArgumentOutput : Original.Ty
  delayedArgumentsTyped : AdaptersTyped pendingDelayedArguments
    pendingArgumentInput pendingArgumentOutput
  bodyResultConsumer : Adapter
  bodyResultType : Original.Ty
  resultAdapterInput : Original.Ty
  resultType : Original.Ty
  bodyResultTyped : contextResultType = bodyResultType
  bodyConsumerInputTyped : bodyResultConsumer.input = bodyResultType
  bodyResultOutputTyped : bodyResultConsumer.output = resultAdapterInput
  pendingResultAdapters : List Adapter
  pendingResultOutput : Original.Ty
  pendingResultsTyped : AdaptersTyped pendingResultAdapters
    resultAdapterInput pendingResultOutput
  finalResultTyped : pendingResultOutput = resultType
  scopeOwner : Nat
  callView : CallView
  literalSuffix : Suffix

structure Request (Suffix World : Type) where
  opInstance : OperationInstance
  payload : Value
  payloadTyped : ValueTyped Original.emptyContext payload opInstance.payloadType
  resultType : Original.Ty
  savedContinuation : Comp
  continuationTyped : CompTyped
    (Original.extend Original.emptyContext opInstance.responseType)
    savedContinuation resultType
  callView : CallView
  scopeContext : List Nat
  viewContext : List ViewOccurrence
  currentWorld : World
  literalSuffix : Suffix

structure Failure where
  reason : Original.Failure

inductive Outcome (Suffix World : Type) where
  | returned (value : Value) (type : Original.Ty)
      (typed : ValueTyped Original.emptyContext value type)
      (currentWorld : World) (literalSuffix : Suffix)
  | requested (request : Request Suffix World)
  | failed (failure : Failure) (resultType : Original.Ty)
      (currentWorld : World) (literalSuffix : Suffix)

end YulangClosure.TypedCall
