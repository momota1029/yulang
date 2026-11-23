import Yulang.GeneralDeclarativeWitnessNestedModel361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 63000
set_option maxHeartbeats 61000000
namespace Yulang.GeneralDeclarativeWitnessMixedForwardChoice361
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessReleasedForward360 (forward forwardKey forwardDemand fixed knownTarget)
open GeneralDeclarativeWitnessJointObservation359 (secondSpan authored secondLo secondHi)
open GeneralDeclarativeWitnessSourceEndpoint359 (Read check_exact endpoint_in_model)
open GeneralDeclarativeWitnessNativePipeline360 (authority)
open GeneralDeclarativeWitnessNativeRelease360 (ExactRelease checkExactRelease checked_exact_written_value)
open GeneralDeclarativeWitnessNativeInstall360 (World Fits NativeViews)
open GeneralDeclarativeWitnessNativeKinds361 (Shaped read)
open GeneralDeclarativeWitnessNativeLeafClassify361 (isHead)
open GeneralDeclarativeWitnessNativeLowerCut361 (levels)
open GeneralDeclarativeWitnessMixedDependency361 (Node Path boardCheck no_strict_loop board_checked)
open GeneralDeclarativeWitnessRank350 (rank check sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeWitnessNativePreparation360 (shape)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCompiler350 (trip)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

def aligned : Declaration :=
  {forward with head := [.var 90,.var 91]}

def visible (r : GeneralDeclarativeWitnessConstructorModes357.Environment) : List Declaration :=
  r.source.declarations.filter (·.role == 7)

structure OrdinarySupported (s : State) : Prop where
  lo : Read authored s 65 secondLo
  hi : Read authored s 66 secondHi
  lowerHead : (GeneralDeclarativeLowerKnown321.constructorTag (secondLo.code 65)).isSome = true
  upperHead : (GeneralDeclarativeLowerKnown321.constructorTag (secondHi.code 66)).isSome = true
  left : Bound s.normal 65 67
  right : Bound s.normal 67 66

def checkOrdinary (s : State) : Bool :=
  GeneralDeclarativeWitnessSourceEndpoint359.check authored s 65 secondLo &&
    GeneralDeclarativeWitnessSourceEndpoint359.check authored s 66 secondHi &&
      decide ((65,67) ∈ s.normal.intervals ∧ (67,66) ∈ s.normal.intervals)

theorem source_inputs_exact {s} (accepted : checkOrdinary s = true) : OrdinarySupported s := by
  have ⟨linked,edges⟩ := Bool.and_eq_true_iff.mp accepted
  have ⟨lo,hi⟩ := Bool.and_eq_true_iff.mp linked
  have bound := of_decide_eq_true edges
  exact ⟨check_exact.mp lo,check_exact.mp hi,rfl,rfl,.interval bound.1,.interval bound.2⟩

structure Choice {negative : Bool} (r : Run negative) (base : World) where
  impl : Declaration
  only : visible r.env = [impl]
  authoredDecl : r.env.source.declarations[forwardKey.sourceOrdinal]? = some impl
  literal : impl = aligned
  constructorsChecked : checkDecl r.env impl = true
  decreaseChecked : shape r.env.source impl = true
  requestChecked : GeneralDeclarativeWitnessProblem349.declared r.env.source forwardDemand = true
  native : ExactRelease base.board authority r.typed.write
  shaped : Shaped r.env r.typed.write.code
  actualHead : isHead r.typed.write.code = true
  exactTarget : r.typed.write.address.target = knownTarget.center
  grounded : OrdinarySupported base.ordinary
  noLoop : ∀ projection n,¬Path base projection true n n

/-- Independent positive decision before recompiling the forwarding
body. First argument uses the installed native point with a current
grant. Second is a separately backed ordinary interval. Both have
actual heads; neither recovers its support from the other argument. -/
def pick {negative} (r : Run negative) (base : World) : Option (Choice r base) :=
  match sole : visible r.env, atDecl : r.env.source.declarations[forwardKey.sourceOrdinal]? with
  | [which],some positioned =>
    if chosen : which = positioned ∧ which = aligned then
      if source : (checkDecl r.env which && shape r.env.source which) &&
          GeneralDeclarativeWitnessProblem349.declared r.env.source forwardDemand then
        if frames : (checkOrdinary base.ordinary && check base.ordinary levels) &&
            boardCheck base (rank levels) 2 then
          if point : r.typed.write.address.target = knownTarget.center ∧ isHead r.typed.write.code = true then do
            let grant ← checkExactRelease base.board authority r.typed.write
            let mode ← read r.env r.typed.write.code
            have hs := Bool.and_eq_true_iff.mp frames
            have readRank := Bool.and_eq_true_iff.mp hs.1
            have literal := congrArg some chosen.1.symm
            have checked := Bool.and_eq_true_iff.mp source
            have cases_ := Bool.and_eq_true_iff.mp checked.1
            some ⟨which,sole,atDecl.trans literal,chosen.2,cases_.1,cases_.2,checked.2,grant,mode,point.2,point.1,
              source_inputs_exact readRank.1,fun _ => no_strict_loop (sound readRank.2) (board_checked hs.2)⟩
          else none
        else none
      else none
    else none
  | _,_ => none

theorem only_reads_two_distinct_source_lanes {negative} {r : Run negative} {base : World}
    (decision : Choice r base) (m : Assignment) (v : NativeViews) (fit : Fits base m v) :
    v knownTarget.center = some (r.typed.write.code.eval m) ∧
    Equivalent (m 65).1 (GeneralDeclarativeWitnessOpenSpine359.sem m (secondLo.code 65)) ∧
    Equivalent (m 66).1 (GeneralDeclarativeWitnessOpenSpine359.sem m (secondHi.code 66)) := by
  have actual := checked_exact_written_value (w := base) decision.native m v fit
  exact ⟨decision.exactTarget ▸ actual,
    endpoint_in_model decision.grounded.lo m fit.1,endpoint_in_model decision.grounded.hi m fit.1⟩

theorem compiler_uses_same_selected_clause {negative} {r : Run negative} {s : Sequence r}
    (selected : Choice r s.ordinaryChild.final) :
    s.continuation.impl = selected.impl ∧
    s.continuation.kids = [s.receiver] ∧
    ((fixed s.ordinaryChild.final).spans.map fun x => (x.1,trip x.2)) =
      [(90,trip knownTarget),(91,trip secondSpan)] := by
  exact ⟨Option.some.inj (s.continuation.authored.symm.trans selected.authoredDecl),s.exactReceiver,rfl⟩

end Yulang.GeneralDeclarativeWitnessMixedForwardChoice361
