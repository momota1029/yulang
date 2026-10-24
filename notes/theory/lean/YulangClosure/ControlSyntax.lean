import YulangClosure.Contracts

namespace YulangClosure.Control

inductive Value where
  | atom (tag data : Nat)
  | no
  | yes (value : Value)
  deriving DecidableEq

structure Operation where
  family : Nat
  instanceId : Nat
  payload : Nat
  response : Nat
  deriving DecidableEq

structure Arm where
  operation : Operation
  code : Nat

structure Handler where
  identity : Nat
  input : Nat
  output : Nat
  valueArms : List Nat
  arms : List Arm

structure Mapper where
  source : Operation
  target : Operation
  payloadCode : Nat
  responseCode : Nat

mutual
  inductive Kont where
    | mk (input : Nat) (frames : List Frame)
  inductive Packet where
    | mk (event : Nat) (operation : Operation) (payload : Value) (saved : Kont)
  inductive Pending where
    | value (value : Value) (remaining : List Nat)
    | request (packet : Packet)
  inductive Action where
    | code (label : Nat)
    | mapped (mapper : Mapper) (original : Packet)
    | response (mapper : Mapper) (original : Kont)
    | enterSaved (mapper : Mapper) (original : Kont)
  inductive Frame where
    | bind (action : Action)
    | scope (owner : Nat)
    | view (identity : Nat)
    | handle (handler : Handler)
    | mapop (mapper : Mapper)
    | wait (handler : Handler) (original : Pending) (remaining : List Arm)
    | release (target : Nat)
end

def Kont.input : Kont → Nat | .mk q _ => q
def Kont.frames : Kont → List Frame | .mk _ fs => fs
def Kont.append (k : Kont) (f : Frame) : Kont := .mk k.input (k.frames ++ [f])
def Packet.operation : Packet → Operation | .mk _ q _ _ => q
def Packet.saved : Packet → Kont | .mk _ _ _ k => k

def Packet.capture : Packet → Frame → Packet
  | .mk e q p k, f => .mk e q p (k.append f)

inductive Head where
  | ret (value : Value)
  | req (packet : Packet)
  | fail (reason : Nat)
  | bad (reason : Nat)
  /-- Registered code may have ordinary Ret/Req/Fail/Bad exits. -/
  | run (label : Nat) (arguments : List Value) (saved : Option Kont)
  | search (handler : Handler) (original : Pending) (remaining : List Arm)

structure State (World : Type) where
  world : World
  head : Head
  stack : List Frame

/-- Only current-world metadata operations, not control transfer or typing laws. -/
structure Metadata (World : Type) where
  scopeReturn : World → Nat → World
  viewReturn : World → Nat → World
  suspendScope : World → Nat → World
  suspendView : World → Nat → World
  releaseCross : World → Nat → Packet → World
  eligible : World → Handler → Arm → Packet → Bool
  /-- Fail cleanup is observationally unspecified in the frozen core. -/
  failWorld : World → Frame → World → Prop
  failWorld_total : ∀ w f, ∃ w', failWorld w f w'

/-- Raw response checking is executable and admits ill-typed responses as Bad. -/
def responseOK (q : Nat) : Value → Bool
  | .atom tag _ => tag == q
  | _ => false

def resume (k : Kont) (value : Value) (world : W) : State W :=
  ⟨world, if responseOK k.input value then .ret value else .bad 0, k.frames⟩

/-- Seven-frame control dispatch. No typing premise occurs in these rules. -/
inductive ControlStep {W : Type} (md : Metadata W) : State W → State W → Prop
  | bindCode : ControlStep md ⟨w,.ret v,.bind (.code c)::fs⟩
      ⟨w,.run c [v] none,fs⟩
  | scopeRet : ControlStep md ⟨w,.ret v,.scope u::fs⟩
      ⟨md.scopeReturn w u,.ret v,fs⟩
  | viewRet : ControlStep md ⟨w,.ret v,.view x::fs⟩
      ⟨md.viewReturn w x,.ret v,fs⟩
  | handleRet : ControlStep md ⟨w,.ret v,.handle h::fs⟩
      ⟨w,.search h (.value v h.valueArms) [],fs⟩
  | mapRet : ControlStep md ⟨w,.ret v,.mapop m::fs⟩ ⟨w,.ret v,fs⟩
  | releaseRet : ControlStep md ⟨w,.ret v,.release t::fs⟩ ⟨w,.ret v,fs⟩
  | waitYes : ControlStep md ⟨w,.ret (.yes v),.wait h pending arms::fs⟩
      ⟨w,.ret v,fs⟩
  | waitNo : ControlStep md ⟨w,.ret .no,.wait h pending arms::fs⟩
      ⟨w,.search h pending arms,fs⟩
  | waitBad : ControlStep md ⟨w,.ret (.atom tag v),.wait h pending arms::fs⟩
      ⟨w,.bad 1,fs⟩
  | bindReq : ControlStep md ⟨w,.req p,.bind a::fs⟩
      ⟨w,.req (p.capture (.bind a)),fs⟩
  | scopeReq : ControlStep md ⟨w,.req p,.scope u::fs⟩
      ⟨md.suspendScope w u,.req (p.capture (.scope u)),fs⟩
  | viewReq : ControlStep md ⟨w,.req p,.view v::fs⟩
      ⟨md.suspendView w v,.req (p.capture (.view v)),fs⟩
  | handleReq : ControlStep md ⟨w,.req p,.handle h::fs⟩
      ⟨w,.search h (.request p) h.arms,fs⟩
  | waitReq : ControlStep md ⟨w,.req p,.wait h original arms::fs⟩
      ⟨w,.req (p.capture (.wait h original arms)),fs⟩
  | releaseReq : ControlStep md ⟨w,.req p,.release t::fs⟩
      ⟨md.releaseCross w t p,.req (p.capture (.release t)),fs⟩
  | mapMiss (hne : q ≠ m.source) :
      ControlStep md ⟨w,.req (.mk e q p k),.mapop m::fs⟩
        ⟨w,.req ((Packet.mk e q p k).capture (.mapop m)),fs⟩
  | mapHit : ControlStep md ⟨w,.req (.mk e m.source p k),.mapop m::fs⟩
      ⟨w,.run m.payloadCode [p] none,.bind (.mapped m (.mk e m.source p k))::fs⟩
  | mappedRet : ControlStep md
      ⟨w,.ret v,.bind (.mapped m (.mk e q p k))::fs⟩
      ⟨w,.req (.mk e m.target v (.mk m.target.response [.bind (.response m k)])),fs⟩
  | responseRet : ControlStep md ⟨w,.ret v,.bind (.response m k)::fs⟩
      ⟨w,.run m.responseCode [v] none,.bind (.enterSaved m k)::fs⟩
  /-- Administrative plugging, NOT a second raw Resume/freshening. -/
  | enterSavedRet : ControlStep md ⟨w,.ret v,.bind (.enterSaved m k)::fs⟩
      ⟨w,.ret v,k.frames ++ .mapop m::fs⟩
  | searchValueTry : ControlStep md ⟨w,.search h (.value v (code::rest)) [],fs⟩
      ⟨w,.run code [v] none,.wait h (.value v rest) []::fs⟩
  | searchValueEnd : ControlStep md ⟨w,.search h (.value v []) [],fs⟩
      ⟨w,.fail 0,fs⟩
  | searchRequestEnd : ControlStep md ⟨w,.search h (.request p) [],fs⟩
      ⟨w,.req (p.capture (.handle h)),fs⟩
  | skip (test : a.operation ≠ p.operation ∨ md.eligible w h a p = false) :
      ControlStep md ⟨w,.search h (.request p) (a::arms),fs⟩
        ⟨w,.search h (.request p) arms,fs⟩
  /-- Selected shallow arm receives original K, with no handle frame appended. -/
  | select (eq : a.operation = q) (yes : md.eligible w h a (.mk e q p k) = true) :
      ControlStep md ⟨w,.search h (.request (.mk e q p k)) (a::arms),fs⟩
        ⟨w,.run a.code [p] (some k),.wait h (.request (.mk e q p k)) arms::fs⟩
  | failRelease : ControlStep md ⟨w,.fail r,.release t::fs⟩ ⟨w,.fail r,fs⟩
  | failFrame (notRelease : ∀ t, f ≠ .release t) (hw : md.failWorld w f w') :
      ControlStep md ⟨w,.fail r,f::fs⟩ ⟨w',.fail r,fs⟩
  | badFrame : ControlStep md ⟨w,.bad r,f::fs⟩ ⟨w,.bad r,fs⟩

/-- Principal-redex relation is limited to registered-code execution.
It cannot dispatch any frame or search state. -/
inductive Step {W : Type} (md : Metadata W)
    (body : W → Nat → List Value → Option Kont → W → Head → Prop) :
    State W → State W → Prop
  | control : ControlStep md s t → Step md body s t
  | body : body w code args saved w' h →
      Step md body ⟨w,.run code args saved,fs⟩ ⟨w',h,fs⟩

end YulangClosure.Control
