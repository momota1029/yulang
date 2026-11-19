import Yulang.GeneralRebaseCertifiedPath266
import Yulang.GeneralRebaseWeakTerminal268

namespace Yulang.GeneralRebaseLullSpine270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Lull Stutter)
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralRebaseCertifiedPath266 (Path edges)

inductive Quiet (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :
 State roles → State roles → Type where
 | nil (state : State roles) : Quiet registry root owners pool state state
 | cons (edge : Edge registry root) :
   project owners pool edge.after = project owners pool edge.before →
   Quiet registry root owners pool edge.after last →
   Quiet registry root owners pool edge.before last

def raw (spine : Quiet registry root owners pool first last) : Path registry root first last :=
 match spine with
 | .nil state => .nil state
 | .cons edge _ rest => .cons edge (raw rest)

theorem sound (spine : Quiet registry root owners pool first last) :
 Lull registry root owners pool first last := by
 induction spine with
 | nil _ => exact .refl
 | cons edge equal _ ih =>
   exact GeneralRebaseWeakTerminal268.append (.tail .refl ⟨edge.actual,equal⟩) ih

def changed (owners : List Nat) (pool : List Output) (edge : Edge registry root) : Bool :=
 decide ((project owners pool edge.before).remaining ≠ (project owners pool edge.after).remaining)

theorem changed_exact (owners : List Nat) (pool : List Output) (edge : Edge registry root) :
 changed owners pool edge = true ↔ project owners pool edge.after ≠ project owners pool edge.before := by
 simp only [changed,decide_eq_true_eq]
 constructor
 · intro diff same
   exact diff (congrArg GeneralRebaseStep258.State.remaining same.symm)
 · intro diff same
   exact diff (GeneralRebaseStep258.state_ext _ _ same.symm)

theorem still_exact (owners : List Nat) (pool : List Output) (edge : Edge registry root) :
 changed owners pool edge = false ↔ project owners pool edge.after = project owners pool edge.before := by
 rw [Bool.eq_false_iff]
 change (¬ changed owners pool edge = true) ↔ _
 rw [changed_exact]
 exact Classical.not_not

end Yulang.GeneralRebaseLullSpine270
