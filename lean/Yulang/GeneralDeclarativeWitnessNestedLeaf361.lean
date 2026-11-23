import Yulang.GeneralDeclarativeWitnessNativeLeafSound361
import Yulang.GeneralDeclarativeWitnessNativeNestedMatch361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 62000
set_option maxHeartbeats 59000000
namespace Yulang.GeneralDeclarativeWitnessNestedLeaf361
open GeneralDeclarativeWitnessNativeNestedMatch361 (Captures Matches read Meaning values)
open GeneralDeclarativeWitnessNativeLeafClassify361 (visible source_visible)
open GeneralDeclarativeWitnessNativePortTransport361 (Port view Part)
open GeneralDeclarativeWitnessNativeDirectSource361 (Wire)
open GeneralDeclarativeWitnessMixedDependency361 (exactGraph Path no_strict_loop board_checked)
open GeneralDeclarativeWitnessRank350 (sound)
open GeneralDeclarativeWitnessScopedBindings359 (slots)
open GeneralDeclarativeWitnessNativePreparation360 (Prepared Layout prepare context)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessSequentialReceiver361 (layout)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessNativePipeline360 (wire)
open GeneralDeclarativeWitnessJointObservation359 (parentScope)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority)
open GeneralDeclarativeWitnessNativeInstall360 (World)
open GeneralDeclarativeWitnessCompiler350 (Finished execute)
open GeneralDeclarativeWitnessLiteral349 (preserves)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Frontier Classify)

def writerSlots {negative} (r : Run negative) :=
  slots [r.prep.captures] parentScope

structure Choice {negative : Bool} {r : Run negative} {s : Sequence r}
    {gate : ReleaseAuthority} {io : Wire} (port : Port s gate io) where
  impl : Declaration
  only : visible s = [impl]
  identity : impl = port.stated.receiver
  pattern : Pattern
  written : impl.head.map normalize = [pattern]
  nested : ∃ key args,pattern = .app key args
  captures : Captures
  matchInput : Matches r.env (writerSlots r) (wire negative).route r.typed.write.code pattern captures
  noKids : impl.requirements = []
  noWrites : impl.associated = [] ∧ s.receiver.outputs = []
  noLoop : ∀ projection n,¬ Path s.final projection true n n

/-- The whole-table source decision for one supported nested input.
The scope and available value come from the real port, not from a compiler
decision. The source match and capture are computed before replay. -/
def elect {negative} {r : Run negative} {s : Sequence r} {gate io} (port : Port s gate io) :
    Option (Choice port) :=
  match sole : visible s with
  | [impl] =>
    have declared : impl = port.stated.receiver := (List.mem_singleton.mp (sole ▸ source_visible port)).symm
    match head : impl.head.map normalize with
    | [.app k args] =>
      if blank : impl.requirements = [] ∧ impl.associated = [] ∧ s.receiver.outputs = [] then
        if graph : exactGraph s then do
          let found ← read r.env (writerSlots r) (wire negative).route r.typed.write.code (.app k args)
          have ranks := Bool.and_eq_true_iff.mp graph
          some ⟨impl,sole,declared,.app k args,head,⟨k,args,rfl⟩,found.1,found.2,blank.1,blank.2,
            fun _ => no_strict_loop (sound ranks.1) (board_checked ranks.2)⟩
        else none
      else none
    | _ => none
  | _ => none

inductive Local {negative : Bool} {r : Run negative} {s : Sequence r}
    {gate : ReleaseAuthority} {io : Wire} (port : Port s gate io) : Demand → Frontier Demand → Prop where
  | terminal (chosen : Choice port) : Local port s.receiver (.selected chosen.impl.id [])

theorem classified {negative} {r : Run negative} {s : Sequence r} {gate io} {port : Port s gate io}
    (c : Choice port) : Classify (Local port) s.receiver (.selected (.node c.impl.id [])) :=
  ⟨.selected c.impl.id [],.selected (.terminal c) .nil,.selected .nil (.selected rfl)⟩

def inputs {negative r s gate io port} (c : @Choice negative r s gate io port) : Layout :=
  {layout s with spans := c.captures}

structure FinishedNested {negative : Bool} {r : Run negative} {s : Sequence r}
    {gate : ReleaseAuthority} {io : Wire} {port : Port s gate io} (c : Choice port) where
  prep : Prepared r.env io.child s.receiver (inputs c)
  sameDecl : prep.impl = c.impl
  body : Finished
  ran : execute (context r.env s.receiver prep.impl (inputs c)) = some body
  noKids : body.kids = []
  noWrites : body.fixed = []
  kept : preserves s.final.ordinary body.state = true

def FinishedNested.world {negative r s gate io port c} (p : @FinishedNested negative r s gate io port c) : World :=
  ⟨p.body.state,s.final.board⟩

def compile {negative} {r : Run negative} {s : Sequence r} {gate io} {port : Port s gate io} (c : Choice port) :
    Option (FinishedNested c) := do
  let prep ← prepare r.env io.child s.receiver (inputs c)
  have exactDecl : prep.impl = c.impl :=
    (Option.some.inj (prep.authored.symm.trans port.stated.targetSource)).trans c.identity.symm
  match ran : execute (context r.env s.receiver prep.impl (inputs c)) with
  | none => none
  | some body =>
    if ok : body.kids = [] ∧ body.fixed = [] ∧ preserves s.final.ordinary body.state = true then
      some ⟨prep,exactDecl,body,ran,ok.1,ok.2.1,ok.2.2⟩
    else none

end Yulang.GeneralDeclarativeWitnessNestedLeaf361
