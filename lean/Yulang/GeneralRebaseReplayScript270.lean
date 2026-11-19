import Yulang.GeneralRebaseReplayCommand270
import Yulang.GeneralRebaseWeakSpine270

namespace Yulang.GeneralRebaseReplayScript270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralSourceState (Output)
open GeneralRebaseReplayCommand270 (Command run edge supported)
open GeneralRebaseCertifiedPath266 (Path)
open GeneralRebaseWeakSpine270 (Spine normalize chooseFirst no_advance_of_none)
open GeneralRebaseWeakProgress268 (Lull Weak)

inductive Script (registry : Registry) (root : Occurrence roles) : State roles → State roles → Type where
 | done (current : State roles) : Script registry root current current
 | execute (cmd : Command registry root first) :
   Script registry root (run cmd) last → Script registry root first last

def path (program : Script registry root first last) : Path registry root first last :=
 match program with
 | .done current => .nil current
 | .execute cmd rest => .cons (edge cmd) (path rest)

def append (before : Script registry root first middle) (after : Script registry root middle last) :
 Script registry root first last :=
 match before with
 | .done _ => after
 | .execute cmd rest => .execute cmd (append rest after)

theorem covers_old (steps : B4Target.Steps (Step registry root) first last) :
 Nonempty (Script registry root first last) := by
 induction steps with
 | refl => exact ⟨.done _⟩
 | tail _ next ih =>
   obtain ⟨prev⟩ := ih
   obtain ⟨cmd,rfl⟩ := supported next
   exact ⟨append prev (.execute cmd (.done _))⟩

def bundle (owners : List Nat) (pool : List Output) (program : Script registry root first last) :
 Spine registry root owners pool first last :=
 normalize owners pool (path program)

def first (owners : List Nat) (pool : List Output) (program : Script registry root start last) :
 Option { after : State _ // Weak registry root owners pool start after } :=
 chooseFirst (bundle owners pool program)

theorem no_hit (owners : List Nat) (pool : List Output) (program : Script registry root start last)
 (h : first owners pool program = none) :
 Lull registry root owners pool start last :=
 (no_advance_of_none (bundle owners pool program) h).2

end Yulang.GeneralRebaseReplayScript270
