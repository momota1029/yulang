import Yulang.GeneralDeclarativeWitnessActualCrossOwnerDictionary363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 79000
set_option maxHeartbeats 100000000
namespace Yulang.GeneralDeclarativeWitnessWhereAlternatives363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root emit)
open GeneralDeclarativeWitnessSelectedNonpointChild363 (Issued backedOccurrence enter)
open GeneralDeclarativeWitnessBareCandidates363 (Covered Decision decideCandidates visible)
open GeneralDeclarativeWitnessNonpointPort362 (author receiver)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessOrderedNonpointRepeat362 (Body replay)
open GeneralDeclarativeWitnessCompiler350 (printDemand trip)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)

def competitor (contra bare : Bool) : Declaration :=
  ⟨99,11,[if bare then .var 93 else .app (GeneralDeclarativeWitnessThreeNative362.ctor contra) [.var 93]],
    [],[],[]⟩

def env (contra bare : Bool) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare {bundle with
    roles := ⟨0,[⟨10,2,[]⟩,⟨11,1,[]⟩]⟩,
    declarations := [author,receiver,competitor contra bare]}

structure Conflict {contra : Bool} {x : Ordered contra} {e : Environment} (r : Root x e) where
  backed : Issued r
  first : Declaration
  second : Declaration
  rest : List Declaration
  exactVisible : visible e r.occurrence = first::second::rest
  apart : first.id ≠ second.id
  full : Covered e r.occurrence (first::second::rest)
  observed : decideCandidates e r.occurrence = some (.ambiguous first second rest exactVisible apart full)

/-- Inspect alternatives after known pre-body input evidence. A raw
compiler can still execute the caller-supplied declaration #98, but
that fact cannot establish election if #99 also matches. -/
def check {contra} {x : Ordered contra} {e : Environment} (r : Root x e) : Option (Conflict r) := do
  let ready ← backedOccurrence r
  match h : decideCandidates e r.occurrence with
  | some (.ambiguous a b rest actual apart full) => some ⟨ready,a,b,rest,actual,apart,full,h⟩
  | _ => none

structure Trial {contra : Bool} (x : Ordered contra) where
  whereEnv : Environment
  root : Root x whereEnv
  conflict : Conflict root
  unselectedBody : Body whereEnv root.world root.occurrence 0
  refused : (enter root).isNone = true

def trial {contra} (x : Ordered contra) : Option (Trial x) := do
  let e ← env contra true
  let root ← emit x e
  let conflict ← check root
  let compilable ← replay e root.world root.occurrence 0
  if refused : (enter root).isNone then some ⟨e,root,conflict,compilable,refused⟩ else none

def actual {contra x} (t : @Trial contra x) : Bool :=
  decide (t.root.chosen.impl.id = 97 ∧
    printDemand t.root.occurrence = (11,[(310,302,311)],[]) ∧
    [t.conflict.first.id,t.conflict.second.id] = [98,99] ∧
    t.unselectedBody.chosen.impl.id = 98 ∧ trip t.unselectedBody.span = (314,302,315))

theorem actual_visible_overlap_despite_successful_forced_replay (contra : Bool) :
    ((run contra).bind fun x => (trial x).map actual).getD false = true := by cases contra <;> decide +kernel

def outside {contra} (x : Ordered contra) : Bool :=
  ((env contra false).map fun e =>
    ((emit x e).map fun root =>
      (backedOccurrence root).isSome &&
        (decideCandidates e root.occurrence).isNone &&
        (replay e root.world root.occurrence 0).isSome &&
        (enter root).isNone).getD false).getD false

theorem unsupported_alternative_not_erased_to_select_first (contra : Bool) :
    ((run contra).map outside).getD false = true := by cases contra <;> decide +kernel

end Yulang.GeneralDeclarativeWitnessWhereAlternatives363
