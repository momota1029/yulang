import Yulang.GeneralDeclarativeWitnessNominalNoFallback364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 94000
set_option maxHeartbeats 131000000
namespace Yulang.GeneralDeclarativeWitnessRealMismatchedRival364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessActualCompoundElection364 (Read check compound)
open GeneralDeclarativeWitnessNonpointPort362 (receiver)
open GeneralDeclarativeWitnessThreeNative362 (ctor)
open GeneralDeclarativeWitnessBareCandidates363 (FitsBare candidate)
open GeneralDeclarativeWitnessOrderedNonpointRepeat362 (Body replay)
open GeneralDeclarativeWitnessCompiler350 (trip)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open GeneralDeclarativeWhere319 (Capture)

structure Result {contra : Bool} (x : Ordered contra) where
  tested : Read x
  elected : tested.inspected.hits = [receiver]
  source : tested.environment.source.declarations[1]? = some receiver
  independentCapture : FitsBare tested.environment tested.sourceRoot.occurrence receiver
  actualSourceArgs : independentCapture.captures = [(92,tested.sourceRoot.span)]
  body : Body tested.environment tested.sourceRoot.world tested.sourceRoot.occurrence 0

/-- Having positively ruled out the *different known nominal*, the
bare receiver is the only applicable row. This is not a preference
for bare syntax and it does not discard an unsupported declaration. -/
def recover {contra} (x : Ordered contra) : Option (Result x) := do
  let t ← check x [receiver,compound (ctor (!contra))]
  if h : t.inspected.hits = [receiver] ∧ t.environment.source.declarations[1]? = some receiver then
    let captured ← candidate t.environment t.sourceRoot.occurrence receiver
    if binds : captured.binders = [92] then
      let raw ← replay t.environment t.sourceRoot.world t.sourceRoot.occurrence 0
      have spans : captured.captures = [(92,t.sourceRoot.span)] := by
        have input : t.sourceRoot.occurrence.arguments = [t.sourceRoot.span] := t.sourceRoot.input
        unfold FitsBare.captures
        rw [binds,input]
        rfl
      pure ⟨t,h.1,h.2,captured,spans,raw⟩
    else none
  else none

theorem actual_fallback_replays_the_independent_span {contra} {x : Ordered contra} (r : Result x) :
    r.body.passed = r.tested.sourceRoot.span ∧
    r.body.chosen.impl = receiver := by
  exact ⟨(List.cons.inj (r.body.args.symm.trans r.tested.sourceRoot.input)).1,r.body.actual⟩

def exact {contra x} (r : @Result contra x) : Bool :=
  decide (r.body.chosen.impl.id = 98 ∧ trip r.body.span = (314,302,315))

theorem actual_bare_winner_after_known_rigid_mismatch (contra : Bool) :
    ((run contra).bind fun x => (recover x).map exact).getD false = true := by
  cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessRealMismatchedRival364
