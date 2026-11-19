import Yulang.GeneralRebaseNestedRecordQuery271

namespace Yulang.GeneralRebaseLocalOriginPocket271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle CandidateCycle)
open GeneralNominalRecursiveInspection (Origin)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots)
open GeneralRebaseOriginRepresentative270 (tightSlot)
open GeneralRebaseNestedRecordQuery271 (resolve resolve_sound)
open GeneralRebaseRecordQuery271 (dead_no_cycle)
open GeneralRebasePartialBool268 (Answer Reflect)

def nominalTargets (state : State roles) (d : GeneralNominalState.Descriptor (Raw state).base.slots) :
 List (Slots state) :=
 d.arguments.filterMap (fun entry => match entry with
    | .type (lo,hi) => tightSlot state lo hi
    | .row _ => none)

def adjacent (state : State roles) (s : Slots state) : List (Slots state) :=
 match (Raw state).nominals s with
 | some d => nominalTargets state d
 | none => match (Raw state).view.heads s with
   | .structural _ child => List.ofFn child
   | _ => []

def nodes (state : State roles) (start : Slots state) : List (Slots state) :=
 FiniteWorklist.reachable (adjacent state) (Raw state).base.slots start

def points (state : State roles) (start : Slots state) :
 Fin (nodes state start).length → Slots state := fun i => (nodes state start)[i]

def checked (state : State roles) (start : Slots state) : Bool :=
 GeneralRebaseFullStructuralWindow271.check state (points state start)

def atSlot (state : State roles) (start : Slots state) : Answer :=
 let w := GeneralRebaseClosedRecordDriver271.window state (points state start)
 GeneralRebaseOriginExecutable269.cyclic w
   (fun o i => GeneralRebaseStructuralRepresentative271.compare state o (w.point i))
   (fun _ => checked state start) (fun _ => false) (origin state start)

theorem atSlot_sound (state : State roles) (full : ∃ m, Models state m) (start : Slots state) :
 Reflect (Cyclic state (origin state start)) (atSlot state start) := by
 let w := GeneralRebaseClosedRecordDriver271.window state (points state start)
 have edge := GeneralRebaseFullStructuralWindow271.edge_sound state _
   (GeneralRebaseStructuralRepresentative271.compare_sound state full)
 have sound : GeneralRebaseOriginCycles268.Sound state w :=
   ⟨fun a b => edge (points state start a) (points state start b) full,full⟩
 unfold atSlot
 exact GeneralRebaseOriginExecutable269.cyclic_sound w sound _ _ _
   (fun i => GeneralRebaseStructuralRepresentative271.compare_sound state full _ _)
   (fun i sure => GeneralRebaseOriginQuotient269.short_closure state w
     (GeneralRebaseFullStructuralWindow271.forward state _ sure full) i)
   (fun falsehood => Bool.noConfusion falsehood)

def inspect (state : State roles) (o : Origin) : Answer :=
 match resolve state o with
 | .dead => some false
 | .child s => atSlot state s
 | .unknown => GeneralRebaseNestedRecordQuery271.inspect state o

theorem inspect_sound (state : State roles) (full : ∃ m, Models state m) (o : Origin) :
 Reflect (Cyclic state o) (inspect state o) := by
 have r := resolve_sound state full o
 unfold inspect
 split
 · rename_i checked
   rw [checked] at r
   exact dead_no_cycle state o r
 · rename_i s checked
   rw [checked] at r
   exact GeneralRebasePartialFinite268.transfer (GeneralRebaseRecordRouting271.cyclic_congr state r).symm
      (atSlot_sound state full s)
 · exact GeneralRebaseNestedRecordQuery271.inspect_sound state full o

def rootOrigin (state : State roles) (focus : Occurrence roles) : Answer :=
 GeneralRebaseVersionedK2Probe268.rootOrigin state focus (inspect state)

theorem rootOrigin_sound (state : State roles) (full : ∃ m, Models state m) (focus : Occurrence roles) :
 Reflect (RootCycle state focus) (rootOrigin state focus) :=
 GeneralRebaseVersionedK2Probe268.rootOrigin_sound state focus _ (inspect_sound state full)

def rootK2 (registry : GeneralDeclarations.Registry) (state : State roles) (focus : Occurrence roles)
 (raw : GeneralRebaseRawK2Probe268.Probes (Raw state)) : Answer :=
 GeneralRebaseVersionedK2Probe268.root registry state focus raw (inspect state)

theorem rootK2_sound (registry : GeneralDeclarations.Registry) (state : State roles) (focus : Occurrence roles)
 (raw : GeneralRebaseRawK2Probe268.Probes (Raw state))
 (validRaw : GeneralRebaseRawK2Probe268.Sound (Raw state) raw) (inhabited : ∃ m, Models state m) :
 Reflect ((GeneralRebaseSourceSurvivor267.Boundary roles).RootK2 registry state focus)
   (rootK2 registry state focus raw) :=
 GeneralRebaseVersionedK2Probe268.root_sound registry state focus raw validRaw _ (inspect_sound state inhabited)

end Yulang.GeneralRebaseLocalOriginPocket271
