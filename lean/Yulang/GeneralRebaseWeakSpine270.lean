import Yulang.GeneralRebaseLullSpine270
import Yulang.GeneralRebaseCertifiedPathCount266
import Yulang.GeneralRebasePathCut266

namespace Yulang.GeneralRebaseWeakSpine270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Weak Lull Counted)
open GeneralRebaseCertifiedObserver266 (Edge chosen chosen_exact)
open GeneralRebaseCertifiedPath266 (Path edges)
open GeneralRebaseLullSpine270 (Quiet raw sound changed changed_exact still_exact)

inductive Spine (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) :
 State roles → State roles → Type where
 | halt : Quiet registry root owners pool first last → Spine registry root owners pool first last
 | advance (edge : Edge registry root) : Quiet registry root owners pool first edge.before →
   project owners pool edge.after ≠ project owners pool edge.before →
   Spine registry root owners pool edge.after last → Spine registry root owners pool first last

def prepend (edge : Edge registry root)
 (still : project owners pool edge.after = project owners pool edge.before)
 (next : Spine registry root owners pool edge.after last) : Spine registry root owners pool edge.before last :=
 match next with
 | .halt stutters => .halt (.cons edge still stutters)
 | .advance stop stutters diff rest => .advance stop (.cons edge still stutters) diff rest

def normalize (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 Spine registry root owners pool first last :=
 match path with
 | .nil state => .halt (.nil state)
 | .cons edge rest =>
   if strict : changed owners pool edge = true then
     .advance edge (.nil _) ((changed_exact ..).mp strict) (normalize owners pool rest)
   else
     prepend edge ((still_exact ..).mp (Bool.eq_false_iff.mpr strict)) (normalize owners pool rest)

def flatten (spine : Spine registry root owners pool first last) : List (Edge registry root) :=
 match spine with
 | .halt stutters => edges (raw stutters)
 | .advance edge stutters _ tail => edges (raw stutters) ++ edge :: flatten tail

theorem prepend_flat (edge : Edge registry root)
 (still : project owners pool edge.after = project owners pool edge.before)
 (next : Spine registry root owners pool edge.after last) :
 flatten (prepend edge still next) = edge :: flatten next := by
 cases next <;> rfl

theorem exact_order (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 flatten (normalize owners pool path) = edges path := by
 induction path with
 | nil => rfl
 | cons edge tail ih =>
   unfold normalize
   split
   · change edge :: flatten (normalize owners pool tail) = edge :: edges tail
     rw [ih]
   · rw [prepend_flat,ih]
     rfl

def count (spine : Spine registry root owners pool first last) : Nat :=
 match spine with
 | .halt _ => 0
 | .advance _ _ _ tail => count tail + 1

theorem prepend_count (edge : Edge registry root)
 (still : project owners pool edge.after = project owners pool edge.before)
 (next : Spine registry root owners pool edge.after last) :
 count (prepend edge still next) = count next := by cases next <;> rfl

theorem match_chosen (owners : List Nat) (pool : List Output) (edge : Edge registry root) :
 changed owners pool edge = chosen owners pool (project owners pool edge.before) edge := by
 rw [Bool.eq_iff_iff,changed_exact,chosen_exact]
 exact ⟨fun h => ⟨rfl,h⟩,And.right⟩

theorem exact_count (owners : List Nat) (pool : List Output) (path : Path registry root first last) :
 count (normalize owners pool path) = GeneralRebaseCertifiedPathCount266.strict_count owners pool path := by
 induction path with
 | nil => rfl
 | cons edge tail ih =>
   rw [GeneralRebasePathCut266.count_cons]
   unfold normalize
   split
   · rename_i hit
     change count (normalize owners pool tail) + 1 = _
     rw [ih,←match_chosen,hit]
     rfl
   · rename_i miss
     rw [prepend_count,ih,←match_chosen,Bool.eq_false_iff.mpr miss]
     simp

theorem old_source (spine : Spine registry root owners pool first last) :
 ∃ middle, Counted registry root owners pool (count spine) first middle ∧ Lull registry root owners pool middle last := by
 induction spine with
 | halt quiet => exact ⟨_,.nil _,sound quiet⟩
 | advance edge stutters diff _ ih =>
   obtain ⟨middle,prior,final⟩ := ih
   exact ⟨middle,GeneralRebaseWeakTerminal268.prepend
       (⟨edge.before,sound stutters,edge.actual,diff⟩ : Weak registry root owners pool _ _) prior,final⟩

def chooseFirst (spine : Spine registry root owners pool first last) :
 Option { after : State _ // Weak registry root owners pool first after } :=
 match spine with
 | .halt _ => none
 | .advance edge quiet diff _ => some ⟨edge.after,edge.before,sound quiet,edge.actual,diff⟩

theorem no_advance_of_none (spine : Spine registry root owners pool first last)
 (no : chooseFirst spine = none) : count spine = 0 ∧ Lull registry root owners pool first last := by
 cases spine with
 | halt quiet => exact ⟨rfl,sound quiet⟩
 | advance _ _ _ _ => cases no

end Yulang.GeneralRebaseWeakSpine270
