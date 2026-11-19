import Yulang.GeneralRebaseOriginRepresentative270

namespace Yulang.GeneralRebaseClosedOriginDriver270
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle)
open GeneralNominalRecursiveInspection (Origin)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseMixedOriginWindow270 (check)
open GeneralRebaseOriginRepresentative270 (window query)
open GeneralRebaseOriginExecutable269 (lookup)

def covered (state : State roles) : Bool := check state (fun i : Slots state => i)

def inspect (state : State roles) (o : Origin) : Answer :=
 if covered state then query state (fun i : Slots state => i) o else none

theorem inspect_sound (state : State roles) (inhabited : ∃ m, Models state m) (o : Origin) :
 Reflect (Cyclic state o) (inspect state o) := by
 unfold inspect
 split
 · rename_i closed
   exact GeneralRebaseOriginRepresentative270.query_sound state _ closed inhabited o
 · trivial

def inspectRoot (state : State roles) (focus : Occurrence roles) : Answer :=
 GeneralRebaseVersionedK2Probe268.rootOrigin state focus (inspect state)

theorem inspectRoot_sound (state : State roles) (inhabited : ∃ m, Models state m) (focus : Occurrence roles) :
 Reflect (RootCycle state focus) (inspectRoot state focus) :=
 GeneralRebaseVersionedK2Probe268.rootOrigin_sound state focus _ (inspect_sound state inhabited)

def rootK2 (registry : GeneralDeclarations.Registry) (state : State roles) (focus : Occurrence roles)
 (raw : GeneralRebaseRawK2Probe268.Probes (Raw state)) : Answer :=
 GeneralRebaseVersionedK2Probe268.root registry state focus raw (inspect state)

theorem rootK2_sound (registry : GeneralDeclarations.Registry) (state : State roles) (focus : Occurrence roles)
 (raw : GeneralRebaseRawK2Probe268.Probes (Raw state))
 (validRaw : GeneralRebaseRawK2Probe268.Sound (Raw state) raw) (inhabited : ∃ m, Models state m) :
 Reflect ((GeneralRebaseSourceSurvivor267.Boundary roles).RootK2 registry state focus)
   (rootK2 registry state focus raw) :=
 GeneralRebaseVersionedK2Probe268.root_sound registry state focus raw validRaw _ (inspect_sound state inhabited)

def totalEdges (state : State roles) : Bool :=
 let w := window state (fun i : Slots state => i)
 (List.finRange (Raw state).base.slots).all (fun x =>
   (List.finRange (Raw state).base.slots).all (fun y => (w.probe x y).isSome))

theorem edges_checked (state : State roles) (total : totalEdges state = true) (x y : Slots state) :
 (window state (fun i : Slots state => i)).probe x y ≠ none := by
 have h := List.all_eq_true.mp (List.all_eq_true.mp total x (List.mem_finRange _)) y (List.mem_finRange _)
 intro absent
 rw [absent] at h
 cases h

def matchSource (state : State roles) (o : Origin) (i : Slots state) : Answer :=
 GeneralRebaseOriginRepresentative270.compare state o (origin state i)

theorem inspect_total (state : State roles) (closed : covered state = true)
 (full : totalEdges state = true) (o : Origin) {i : Slots state} (found : lookup (matchSource state) o = some i) :
 inspect state o ≠ none := by
 have total := GeneralRebasePartialCycles268.evaluate_total
   (window state (fun j : Slots state => j)).probe (edges_checked state full) i
 unfold inspect
 simp only [closed,ite_true]
 apply GeneralRebasePartialBool268.total_both
 · change GeneralRebaseOriginExecutable269.graphQuery _ (matchSource state) _ _ o ≠ none
   unfold GeneralRebaseOriginExecutable269.graphQuery
   rw [found]
   unfold GeneralRebaseOriginCycles268.graph
   cases answer : GeneralRebasePartialCycles268.evaluate (window state (fun j : Slots state => j)).probe i with
   | none => exact False.elim (total answer)
   | some b => cases b <;> simp [answer]
 · simp [window,GeneralRebaseMixedOriginWindow270.window]

theorem inspect_exact (state : State roles) (inhabited : ∃ m, Models state m)
 (closed : covered state = true) (full : totalEdges state = true)
 (o : Origin) {i : Slots state} (found : lookup (matchSource state) o = some i) :
 inspect state o = some true ↔ Cyclic state o :=
 GeneralRebasePartialBool268.true_iff (inspect_sound state inhabited o) (inspect_total state closed full o found)

end Yulang.GeneralRebaseClosedOriginDriver270
