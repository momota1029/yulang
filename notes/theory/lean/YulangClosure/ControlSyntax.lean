import YulangClosure.Contracts
import YulangClosure.CoreExecution

namespace YulangClosure.Control

inductive Value where
  | atom (tag data : Nat)
  | no
  | yes (value : Value)
  /-- A value in the explicitly proved Original fragment, retained as syntax. -/
  | originalValue (value : Original.Val)

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
    /-- A source bind frame in the delimited Original fragment. -/
    | originalBind (body : Original.Comp)
    /-- Typed Call frames remain executable syntax while using the existing
        metadata world operations for failure propagation. -/
    | typedCallBind (body : TypedCall.Comp)
    | typedCallAdapter (input output : Original.Ty) (body : TypedCall.Comp)
    /-- Metatheoretic delimiter between source frames and a foreign suffix. -/
    | originalBoundary
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
  /-- Original computations remain their actual syntax during source execution. -/
  | original (computation : Original.Comp)
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

/-- Actual source-derived Call phases.  The Call execution stack is separate
from the independently typed Control suffix carried by `CallState`. -/
inductive CallHead where
  | call (term : TypedCall.CallTerm)
  | enter (function : TypedCall.Function) (carrier : TypedCall.Value)
      (pendingResults : List TypedCall.Adapter)
  | received (function : TypedCall.Function) (carrier : TypedCall.Value)
      (pendingResults : List TypedCall.Adapter)
  | active (computation : TypedCall.Comp)
  | originalState (state : Original.State)
  | returned (value : TypedCall.Value)
  | requesting (opInstance : TypedCall.OperationInstance) (payload : TypedCall.Value)
      (continuation : TypedCall.Comp) (observedViews : List TypedCall.ViewOccurrence)
  | requested (opInstance : TypedCall.OperationInstance) (payload : TypedCall.Value)
      (continuation : TypedCall.Comp)
  | failed (reason : Original.Failure)

structure CallState (World : Type) where
  world : World
  head : CallHead
  frames : List TypedCall.ContextFrame
  callView : TypedCall.CallView
  resultType : Original.Ty
  scopeContext : List Nat
  viewContext : List TypedCall.ViewOccurrence
  receiptSlots : List TypedCall.ReceiptSlot
  literalSuffix : List Frame

def CallState.suffixViewIds : List Frame → List Nat
  | [] => []
  | .view identity :: frames => identity :: suffixViewIds frames
  | _ :: frames => suffixViewIds frames

def CallState.initial {World : Type} (term : TypedCall.CallTerm) (world : World)
    (suffix : List Frame) : CallState World :=
  ⟨world, .call term, [], term.callView, term.resultType, [],
    term.argument.occurrences ++ term.callView.capturedViews,
    term.argument.receipts, suffix⟩

def CallState.captureBind (continuation body : TypedCall.Comp) : TypedCall.Comp :=
  .bind continuation (TypedCall.renameCallComp (TypedCall.upCall Nat.succ) body)

def CallState.contextControlFrame : TypedCall.ContextFrame → Frame
  | .bind body => .typedCallBind body
  | .scope owner => .scope owner
  | .expose effectView _ => .view effectView.identity
  | .adapter input output body => .typedCallAdapter input output body

def CallState.activeViews (frames : List TypedCall.ContextFrame) :
    List TypedCall.ViewOccurrence :=
  frames.filterMap fun frame =>
    match frame with
    | .expose effectView _ => some effectView
    | _ => none

/-- The source Call and all its administrative/body transitions are reachable
with a literal independently typed Control suffix.  Metadata operations are
the already existing Control world operations; this relation introduces no
new failure cleanup or event policy. -/
inductive CallControlStep {World : Type} (md : Metadata World) :
    CallState World → CallState World → Prop where
  | start (term : TypedCall.CallTerm) (world : World) (suffix : List Frame) :
      CallControlStep md (CallState.initial term world suffix)
        ⟨world, .enter term.function term.argument.underlying [],
          (term.callView.interfaces.reverse.map fun interface =>
            TypedCall.ContextFrame.expose interface.ports.callEffectView
              interface.ports.resultView) ++
            [.scope term.callView.receiverOwner],
          term.callView, term.resultType, [],
          term.argument.occurrences ++ term.callView.capturedViews,
          term.argument.receipts, suffix⟩
  | peelWrap (world : World) (inner : TypedCall.Function)
      (argumentAdapter resultAdapter : TypedCall.Adapter)
      (carrier : TypedCall.Value) (pending : List TypedCall.Adapter)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .enter (.wrap inner argumentAdapter resultAdapter) carrier pending,
          frames, view, result, scopes, views, receipts, suffix⟩
        ⟨world, .enter inner (TypedCall.delayArgument carrier argumentAdapter)
          (resultAdapter :: pending), frames, view, result, scopes, views, receipts, suffix⟩
  | attachReceipt (world : World) (mode : Original.Mode)
      (receipt : TypedCall.ReceiptTemplate) (argument bodyResult result : Original.Ty)
      (body : TypedCall.Comp) (consumer : TypedCall.Adapter)
      (functionTyped : TypedCall.FunctionTyped
        (.lambda mode receipt argument bodyResult result body consumer)
        argument result)
      (carrier : TypedCall.Value) (pending : List TypedCall.Adapter)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (resultType : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .enter
          (.lambda mode receipt argument bodyResult result body consumer)
          carrier pending, frames, view, resultType, scopes, views, receipts, suffix⟩
        ⟨world, .received
          (.lambda mode receipt argument bodyResult result body consumer)
          carrier pending, frames, view, resultType, scopes, views,
          receipts ++ receipt.designatedSlots, suffix⟩
  | enterLambda (world : World) (mode : Original.Mode)
      (receipt : TypedCall.ReceiptTemplate) (argument bodyResult result : Original.Ty)
      (body : TypedCall.Comp) (consumer : TypedCall.Adapter)
      (functionTyped : TypedCall.FunctionTyped
        (.lambda mode receipt argument bodyResult result body consumer)
        argument result)
      (carrier : TypedCall.Value) (pending : List TypedCall.Adapter)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (resultType : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .received
          (.lambda mode receipt argument bodyResult result body consumer)
          carrier pending, frames, view, resultType, scopes, views, receipts, suffix⟩
        ⟨world, .active (TypedCall.callEntryBody mode carrier body consumer pending),
          frames, view, resultType, scopes, views, receipts, suffix⟩
  | enterBind (world : World) (first body : TypedCall.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.bind first body), frames, view, result, scopes, views,
          receipts, suffix⟩
        ⟨world, .active first, .bind body :: frames, view, result, scopes, views,
          receipts, suffix⟩
  | enterOriginal (world : World) (body : Original.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.original body), frames, view, result, scopes, views,
          receipts, suffix⟩
        ⟨world, .originalState ⟨body, []⟩, frames, view, result, scopes, views,
          receipts, suffix⟩
  | originalStep (world : World) (source target : Original.State)
      (step : Original.Step source target) (frames : List TypedCall.ContextFrame)
      (view : TypedCall.CallView) (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .originalState source, frames, view, result, scopes, views, receipts,
          suffix⟩
        ⟨world, .originalState target, frames, view, result, scopes, views, receipts,
          suffix⟩
  | originalExit (world : World) (value : Original.Val)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .originalState ⟨.ret value, []⟩, frames, view, result, scopes, views,
          receipts, suffix⟩
        ⟨world, .active (.ret (.original value)), frames, view, result, scopes, views,
          receipts, suffix⟩
  | enterScope (world : World) (owner : Nat) (body : TypedCall.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.scope owner body), frames, view, result, scopes, views,
          receipts, suffix⟩
        ⟨world, .active body, .scope owner :: frames, view, result, scopes,
          views, receipts, suffix⟩
  | enterExpose (world : World) (effectView resultView : TypedCall.ViewOccurrence)
      (body : TypedCall.Comp) (frames : List TypedCall.ContextFrame)
      (view : TypedCall.CallView) (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.expose effectView resultView body), frames, view, result,
          scopes, views, receipts, suffix⟩
        ⟨world, .active body, .expose effectView resultView :: frames, view, result,
          scopes, views, receipts, suffix⟩
  | emitRequest (world : World) (opInstance : TypedCall.OperationInstance)
      (payload : TypedCall.Value) (continuation : TypedCall.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffixViews : List TypedCall.ViewOccurrence)
      (suffixViewMatch : suffixViews.map TypedCall.ViewOccurrence.identity =
        CallState.suffixViewIds suffix)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.request opInstance payload continuation), frames, view, result,
          scopes, views, receipts, suffix⟩
        ⟨world, .requesting opInstance payload continuation
          (views ++ CallState.activeViews frames ++ suffixViews), frames, view, result,
          scopes, views ++ CallState.activeViews frames ++ suffixViews, receipts, suffix⟩
  | forceDelay (world : World) (body : TypedCall.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.force (.delay body)), frames, view, result, scopes, views,
          receipts, suffix⟩
        ⟨world, .active body, frames, view, result, scopes, views, receipts, suffix⟩
  | returnBind (world : World) (value : TypedCall.Value) (body : TypedCall.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.ret value), .bind body :: frames, view, result, scopes,
          views, receipts, suffix⟩
        ⟨world, .active (TypedCall.substituteCallComp
          (fun index => if index = 0 then value else .var (index - 1)) body),
          frames, view, result, scopes, views, receipts, suffix⟩
  | returnAdapter (world : World) (value : TypedCall.Value)
      (input output : Original.Ty) (body : TypedCall.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.ret value), .adapter input output body :: frames, view,
          result, scopes, views, receipts, suffix⟩
        ⟨world, .active (TypedCall.substituteCallComp
          (fun index => if index = 0 then value else .var (index - 1)) body),
          frames, view, result, scopes, views, receipts, suffix⟩
  | returnScope (world : World) (owner : Nat) (value : TypedCall.Value)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.ret value), .scope owner :: frames, view, result, scopes,
          views, receipts, suffix⟩
        ⟨md.scopeReturn world owner, .active (.ret value), frames, view, result,
          scopes, views, receipts, suffix⟩
  | returnExpose (world : World) (effectView resultView : TypedCall.ViewOccurrence)
      (value : TypedCall.Value) (frames : List TypedCall.ContextFrame)
      (view : TypedCall.CallView) (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.ret value), .expose effectView resultView :: frames,
          view, result, scopes, views, receipts, suffix⟩
        ⟨md.viewReturn world resultView.identity, .active (.ret (.view value resultView)),
          frames, view, result, scopes, views, receipts, suffix⟩
  | requestBind (world : World) (opInstance : TypedCall.OperationInstance)
      (payload : TypedCall.Value) (continuation body : TypedCall.Comp)
      (observed : List TypedCall.ViewOccurrence)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .requesting opInstance payload continuation observed,
          .bind body :: frames, view, result, scopes, views, receipts, suffix⟩
        ⟨world, .requesting opInstance payload
          (CallState.captureBind continuation body) observed,
          frames, view, result, scopes, views, receipts, suffix⟩
  | requestAdapter (world : World) (opInstance : TypedCall.OperationInstance)
      (payload : TypedCall.Value) (continuation : TypedCall.Comp)
      (observed : List TypedCall.ViewOccurrence)
      (input output : Original.Ty) (body : TypedCall.Comp)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .requesting opInstance payload continuation observed,
          .adapter input output body :: frames, view, result, scopes, views, receipts,
          suffix⟩
        ⟨world, .requesting opInstance payload
          (CallState.captureBind continuation body) observed,
          frames, view, result, scopes, views, receipts, suffix⟩
  | requestScope (world : World) (owner : Nat)
      (opInstance : TypedCall.OperationInstance) (payload : TypedCall.Value)
      (continuation : TypedCall.Comp)
      (observed : List TypedCall.ViewOccurrence)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .requesting opInstance payload continuation observed,
          .scope owner :: frames, view, result, scopes, views, receipts, suffix⟩
        ⟨md.suspendScope world owner,
          .requesting opInstance payload (.scope owner continuation) observed, frames,
          view, result, owner :: scopes, views, receipts, suffix⟩
  | requestExpose (world : World) (effectView resultView : TypedCall.ViewOccurrence)
      (opInstance : TypedCall.OperationInstance) (payload : TypedCall.Value)
      (continuation : TypedCall.Comp)
      (observed : List TypedCall.ViewOccurrence)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .requesting opInstance payload continuation observed,
          .expose effectView resultView :: frames, view, result, scopes, views,
          receipts, suffix⟩
        ⟨md.suspendView world effectView.identity,
          .requesting opInstance payload
            (.expose effectView resultView continuation) observed,
          frames, view, result, scopes, views, receipts, suffix⟩
  | failBind (world : World) (reason : Original.Failure) (body : TypedCall.Comp)
      (nextWorld : World) (cleanup : md.failWorld world (.typedCallBind body) nextWorld)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.fail reason), .bind body :: frames, view, result, scopes,
          views, receipts, suffix⟩
        ⟨nextWorld, .active (.fail reason), frames, view, result, scopes, views,
          receipts, suffix⟩
  | failAdapter (world : World) (reason : Original.Failure)
      (input output : Original.Ty) (body : TypedCall.Comp)
      (nextWorld : World)
      (cleanup : md.failWorld world (.typedCallAdapter input output body) nextWorld)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.fail reason), .adapter input output body :: frames,
          view, result, scopes, views, receipts, suffix⟩
        ⟨nextWorld, .active (.fail reason), frames, view, result, scopes, views,
          receipts, suffix⟩
  | failScope (world : World) (reason : Original.Failure) (owner : Nat)
      (nextWorld : World) (cleanup : md.failWorld world (.scope owner) nextWorld)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.fail reason), .scope owner :: frames, view, result, scopes,
          views, receipts, suffix⟩
        ⟨nextWorld, .active (.fail reason), frames, view, result, scopes, views,
          receipts, suffix⟩
  | failExpose (world : World) (reason : Original.Failure)
      (effectView resultView : TypedCall.ViewOccurrence)
      (nextWorld : World)
      (cleanup : md.failWorld world (.view effectView.identity) nextWorld)
      (frames : List TypedCall.ContextFrame) (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.fail reason), .expose effectView resultView :: frames,
          view, result, scopes, views, receipts, suffix⟩
        ⟨nextWorld, .active (.fail reason), frames, view, result, scopes, views,
          receipts, suffix⟩
  | finishReturn (world : World) (value : TypedCall.Value)
      (view : TypedCall.CallView) (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.ret value), [], view, result, scopes, views, receipts, suffix⟩
        ⟨world, .returned value, [], view, result, scopes, views, receipts, suffix⟩
  | finishRequest (world : World) (opInstance : TypedCall.OperationInstance)
      (payload : TypedCall.Value) (continuation : TypedCall.Comp)
      (observed : List TypedCall.ViewOccurrence)
      (view : TypedCall.CallView)
      (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .requesting opInstance payload continuation observed, [], view, result,
          scopes, views, receipts, suffix⟩
        ⟨world, .requested opInstance payload continuation, [], view, result, scopes,
          observed, receipts, suffix⟩
  | finishFailure (world : World) (reason : Original.Failure)
      (view : TypedCall.CallView) (result : Original.Ty) (scopes : List Nat)
      (views : List TypedCall.ViewOccurrence) (receipts : List TypedCall.ReceiptSlot)
      (suffix : List Frame) :
      CallControlStep md
        ⟨world, .active (.fail reason), [], view, result, scopes, views, receipts, suffix⟩
        ⟨world, .failed reason, [], view, result, scopes, views, receipts, suffix⟩

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
  | originalEnter : ControlStep md ⟨w,.original (.bind first body),fs⟩
      ⟨w,.original first,.originalBind body::fs⟩
  | originalReturnBind : ControlStep md
      ⟨w,.original (.ret value),.originalBind body::fs⟩
      ⟨w,.original (Original.substComp (Original.single value) body),fs⟩
  | originalPrincipal : Original.Principal first next → ControlStep md
      ⟨w,.original first,fs⟩ ⟨w,.original next,fs⟩
  | originalExit : ControlStep md
      ⟨w,.original (.ret value),.originalBoundary::fs⟩
      ⟨w,.ret (.originalValue value),fs⟩

/-- Principal-redex relation is limited to registered-code execution.
It cannot dispatch any frame or search state. -/
inductive Step {W : Type} (md : Metadata W)
    (body : W → Nat → List Value → Option Kont → W → Head → Prop) :
    State W → State W → Prop
  | control : ControlStep md s t → Step md body s t
  | body : body w code args saved w' h →
      Step md body ⟨w,.run code args saved,fs⟩ ⟨w',h,fs⟩

end YulangClosure.Control
