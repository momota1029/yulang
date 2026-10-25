import YulangClosure.CoreSyntax

namespace YulangClosure.HigherOrder
open YulangClosure.Original (Base)

inductive Ty where
  | base (kind : Base)
  | thunk (result : Ty)
  | union (left right : Ty)
  | intersection (left right : Ty)
  | top | bottom
  | callable (argument result : Ty)

inductive PortKind where
  | carrier | callEffect | result
  deriving DecidableEq

/-- A source path is a sequence of structural component labels followed by a
typed semantic port. -/
structure PortPath where
  components : List Nat
  port : PortKind
  type : Ty

structure ViewOccurrence where
  identity : Nat
  path : PortPath

inductive PathRule : PortPath → PortPath → Prop where
  | identity (p : PortPath) : PathRule p p
  | prefix (label : Nat) (p q : PortPath) :
      PathRule p q → PathRule ⟨label :: p.components, p.port, p.type⟩
        ⟨label :: q.components, q.port, q.type⟩
  | adapterMap (mappingIdentity : Nat) (p q : PortPath) : PathRule p q

/-- Endpoints are data and the rule remains Prop-valued metadata. This does
not recover an erased adapterMap identity as runtime data. Syntax is typing-proof-free,
not entirely proof-free. The permissive old adapterMap relation is retained. -/
structure PathCorrespondence where
  source : PortPath
  target : PortPath
  rule : PathRule source target

structure OperationInstance where
  operation : Nat
  typeArguments : List Ty
  payloadType : Ty
  responseType : Ty

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

mutual
  inductive Value where
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
    | inLeft (value : Value)
    | inRight (value : Value)
    | both (value : Value)
    | top (value : Value)
    | view (value : Value) (occurrence : ViewOccurrence)
    | lambda (mode : Original.Mode) (receipt : ReceiptTemplate)
        (argument bodyResult result : Ty) (body : Comp) (consumer : Adapter)
    | wrap (inner : Value) (input output : Adapter)
  inductive Comp where
    | ret (value : Value)
    | force (value : Value)
    | bind (first body : Comp)
    | unionCase (value : Value) (left right : Comp)
    | chooseLeft (value : Value)
    | chooseRight (value : Value)
    | absurd (value : Value)
    | scope (owner : Nat) (body : Comp)
    | expose (effectView resultView : ViewOccurrence) (body : Comp)
    | request (op : OperationInstance) (payload : Value) (continuation : Comp)
    | fail (reason : Original.Failure)
    | dynamicCall (function argument : Value)
  inductive Adapter where
    | mk (input output : Ty) (body : Comp)
        (paths : List PathCorrespondence) (views : List ViewOccurrence)
end

abbrev Context := Nat → Option Ty

def emptyContext : Context := fun _ => none

def extend (env : Context) (a : Ty) : Context
  | 0 => some a
  | n+1 => env n

mutual
  inductive ValueTyped : Context → Value → Ty → Prop
    | var : env i = some a → ValueTyped env (.var i) a
    | unit : ValueTyped env .unit (.base .unit)
    | bool : ValueTyped env (.bool v) (.base .bool)
    | int : ValueTyped env (.int v) (.base .int)
    | floatBits : ValueTyped env (.floatBits v) (.base .float)
    | string : ValueTyped env (.string v) (.base .string)
    | bytes : ValueTyped env (.bytes v) (.base .bytes)
    | path : ValueTyped env (.path v) (.base .path)
    | char : ValueTyped env (.char v) (.base .char)
    | delay : CompTyped env m a → ValueTyped env (.delay m) (.thunk a)
    | inLeft : ValueTyped env v a → ValueTyped env (.inLeft v) (.union a b)
    | inRight : ValueTyped env v b → ValueTyped env (.inRight v) (.union a b)
    | both : ValueTyped env v a → ValueTyped env v b →
        ValueTyped env (.both v) (.intersection a b)
    | top : ValueTyped env v a → ValueTyped env (.top v) .top
    | view : ValueTyped env v a → ValueTyped env (.view v occurrence) a
    | lambdaValue : CompTyped (extend env a) body b → AdapterTyped env consumer b r →
        ValueTyped env (.lambda .value receipt a b r body consumer) (.callable a r)
    | lambdaComputation : CompTyped (extend env (.thunk a)) body b → AdapterTyped env consumer b r →
        ValueTyped env (.lambda .computation receipt a b r body consumer) (.callable a r)
    | wrap : ValueTyped env f (.callable a b) → AdapterTyped env input c a →
        AdapterTyped env output b d → ValueTyped env (.wrap f input output) (.callable c d)
  inductive CompTyped : Context → Comp → Ty → Prop
    | ret : ValueTyped env v a → CompTyped env (.ret v) a
    | force : ValueTyped env v (.thunk a) → CompTyped env (.force v) a
    | bind : CompTyped env m a → CompTyped (extend env a) n b →
        CompTyped env (.bind m n) b
    | unionCase : ValueTyped env v (.union a b) →
        CompTyped (extend env a) l c → CompTyped (extend env b) r c →
        CompTyped env (.unionCase v l r) c
    | chooseLeft : ValueTyped env v (.intersection a b) → CompTyped env (.chooseLeft v) a
    | chooseRight : ValueTyped env v (.intersection a b) → CompTyped env (.chooseRight v) b
    | absurd : ValueTyped env v .bottom → CompTyped env (.absurd v) a
    | scope : CompTyped env body a → CompTyped env (.scope owner body) a
    | expose : CompTyped env body a → CompTyped env (.expose ev rv body) a
    | request : ValueTyped env payload op.payloadType →
        CompTyped (extend env op.responseType) continuation a →
        CompTyped env (.request op payload continuation) a
    | fail : CompTyped env (.fail reason) a
    | dynamicCall : ValueTyped env f (.callable a b) → ValueTyped env arg (.thunk a) →
        CompTyped env (.dynamicCall f arg) b
  inductive AdapterTyped : Context → Adapter → Ty → Ty → Prop where
    | mk : CompTyped (extend env a) body b →
        AdapterTyped env (.mk a b body paths views) a b
end


end YulangClosure.HigherOrder
