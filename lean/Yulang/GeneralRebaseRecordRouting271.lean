import Yulang.GeneralRebaseRecordQuery271
import Yulang.GeneralRebaseClosedRecordDriver271

namespace Yulang.GeneralRebaseRecordRouting271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic Equal RootCycle CandidateCycle)
open GeneralNominalRecursiveInspection (Origin)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseNominalOrigin269 (origin)
open GeneralRebaseRecordQuery271 (locate locate_sound dead_no_cycle)
open GeneralRebasePartialBool268 (Answer Reflect)

theorem cyclic_congr (state : State roles) (equal : Equal state a b) : Cyclic state a ↔ Cyclic state b :=
 ⟨fun ⟨loop,model⟩ => ⟨(GeneralRebaseOriginQuotient269.nonempty_cycle_iff state equal).mp loop,model⟩,
  fun ⟨loop,model⟩ => ⟨(GeneralRebaseOriginQuotient269.nonempty_cycle_iff state equal).mpr loop,model⟩⟩

/-- Only checked freshly represented record origins are rewritten.
Malformed or shadowed positions can exclude a cycle before graph closure. -/
def inspect (state : State roles) (o : Origin) : Answer :=
 match locate state o with
 | .dead => some false
 | .child s => GeneralRebaseClosedRecordDriver271.inspect state (origin state s)
 | .unknown => GeneralRebaseClosedRecordDriver271.inspect state o

theorem inspect_sound (state : State roles) (full : ∃ m, Models state m) (o : Origin) :
 Reflect (Cyclic state o) (inspect state o) := by
 have r := locate_sound state full o
 unfold inspect
 split
 · rename_i checked
   rw [checked] at r
   exact dead_no_cycle state o r
 · rename_i s checked
   rw [checked] at r
   exact GeneralRebasePartialFinite268.transfer (cyclic_congr state r).symm
      (GeneralRebaseClosedRecordDriver271.inspect_sound state full (origin state s))
 · exact GeneralRebaseClosedRecordDriver271.inspect_sound state full o

def inspectRoot (state : State roles) (focus : Occurrence roles) : Answer :=
 GeneralRebaseVersionedK2Probe268.rootOrigin state focus (inspect state)

theorem inspectRoot_sound (state : State roles) (full : ∃ m, Models state m) (focus : Occurrence roles) :
 Reflect (RootCycle state focus) (inspectRoot state focus) :=
 GeneralRebaseVersionedK2Probe268.rootOrigin_sound state focus _ (inspect_sound state full)

def candidates (state : State roles) (plans : List (GeneralNominalCenters.Plan roles))
 (frame : GeneralNominalCenters.Plan roles → Answer) : Answer :=
 GeneralRebaseVersionedK2Probe268.candidateOrigin plans frame (inspect state)

theorem candidates_sound (registry : GeneralDeclarations.Registry) (state : State roles) (focus : Occurrence roles)
 (plans : List (GeneralNominalCenters.Plan roles)) (frame : GeneralNominalCenters.Plan roles → Answer)
 (meaning : ∀ plan ∈ plans, Reflect (GeneralRebaseVersionedK2Probe268.framed registry state focus plan) (frame plan))
 (support : ∀ plan, GeneralRebaseVersionedK2Probe268.framed registry state focus plan → plan ∈ plans)
 (full : ∃ m, Models state m) :
 Reflect (CandidateCycle (GeneralRebaseSourceSurvivor267.Encoded registry) state focus)
  (candidates state plans frame) :=
 GeneralRebaseVersionedK2Probe268.candidateOrigin_sound registry state focus plans frame (inspect state)
    meaning support (inspect_sound state full)

end Yulang.GeneralRebaseRecordRouting271
