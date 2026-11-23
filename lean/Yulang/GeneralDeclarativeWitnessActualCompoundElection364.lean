import Yulang.GeneralDeclarativeWitnessCompoundCandidate364
import Yulang.GeneralDeclarativeWitnessWhereAlternatives363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 85000
set_option maxHeartbeats 115000000
namespace Yulang.GeneralDeclarativeWitnessActualCompoundElection364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root emit)
open GeneralDeclarativeWitnessOriginalEndpointProjection364 (Projection project)
open GeneralDeclarativeWitnessCompoundCandidate364 (Trace scan)
open GeneralDeclarativeWitnessBareCandidates363 (visible)
open GeneralDeclarativeWitnessNonpointPort362 (author receiver)
open GeneralDeclarativeWitnessThreeNative362 (ctor)
open GeneralDeclarativeWitnessCoverageFixture357 (bundle)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarations (Declaration)

def compound (key : Nat) : Declaration := ⟨99,11,[.app key [.var 93]],[],[],[]⟩
def unsupported : Declaration := ⟨100,11,[.app 90 []],[],[],[]⟩

def source (xs : List Declaration) : Option Environment :=
  GeneralDeclarativeWitnessCoverageFixture357.prepare
    {bundle with roles := ⟨0,[⟨10,2,[]⟩,⟨11,1,[]⟩]⟩,declarations := author::xs}

structure Read {contra : Bool} (x : Ordered contra) where
  environment : Environment
  sourceRoot : Root x environment
  independently : Projection sourceRoot
  inspected : Trace independently (visible environment sourceRoot.occurrence)

def check {contra} (x : Ordered contra) (xs : List Declaration) : Option (Read x) := do
  let e ← source xs
  let r ← emit x e
  let p ← project r
  let found ← scan p (visible e r.occurrence)
  pure ⟨e,r,p,found⟩

def outcomes {contra x} (t : @Read contra x) : List Nat :=
  t.inspected.hits.map (·.id)

def actual {contra} (x : Ordered contra) : Bool :=
  decide (((check x [compound (ctor contra)]).map outcomes) = some [99] ∧
    ((check x [receiver,compound (ctor contra)]).map outcomes) = some [98,99] ∧
    ((check x [receiver,compound (ctor (!contra))]).map outcomes) = some [98] ∧
    ((check x [receiver,unsupported]).map outcomes) = none)

theorem actual_visible_source_controls (contra : Bool) :
    ((run contra).map actual).getD false = true := by cases contra <;> decide +kernel

theorem unique_is_not_just_well_formed {contra} {x : Ordered contra} (t : Read x) {row : Declaration}
    (only : t.inspected.hits = [row]) :
    ∀ other,other ∈ t.inspected.hits → other = row := by
  rw [only]
  intro _ h
  exact List.mem_singleton.mp h

end Yulang.GeneralDeclarativeWitnessActualCompoundElection364
