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
