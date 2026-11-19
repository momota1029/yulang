import Yulang.GeneralRebaseWeakProgress268

namespace Yulang.GeneralRebaseWeakTerminal268
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseWeakProgress268 (Weak Lull Counted lull_same lull_source weak_source)

def Terminal (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (state : State roles) : Prop := ∀ after, ¬ Weak registry root owners pool state after

theorem counted_fixed (terminal : Terminal registry root owners pool first)
 (path : Counted registry root owners pool count first last) : last = first := by
 induction path with
 | nil _ => rfl
 | tail _ next ih =>
   rw [ih terminal] at next
   exact False.elim (terminal _ next)

theorem terminal_iff (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (state : State roles) :
 Terminal registry root owners pool state ↔
 ∀ after, B4Target.Steps (Step registry root) state after → project owners pool after = project owners pool state := by
 constructor
 · intro terminal after path
   obtain ⟨_,last,counted,stutter,_⟩ := GeneralRebaseWeakProgress268.decomposition registry root owners pool path
   exact (lull_same stutter).trans (congrArg (project owners pool) (counted_fixed terminal counted))
 · intro all after move
   obtain ⟨mid,stutter,step,different⟩ := move
   exact different ((all after (.tail (lull_source stutter) step)).trans (all mid (lull_source stutter)).symm)

theorem append {R : α → α → Prop} (earlier : B4Target.Steps R first middle)
 (later : B4Target.Steps R middle last) : B4Target.Steps R first last := by
 induction later with
 | refl => exact earlier
 | tail _ edge ih => exact .tail ih edge

theorem terminal_after_stutters (terminal : Terminal registry root owners pool first)
 (stutter : Lull registry root owners pool first mid) : Terminal registry root owners pool mid := by
 intro after move
 obtain ⟨target,tail,step,different⟩ := move
 have prior := append stutter tail
 exact terminal after ⟨target,prior,step,different⟩


theorem counted_old (path : Counted registry root owners pool count first last) :
 B4Target.Steps (Step registry root) first last := by
 induction path with
 | nil _ => exact .refl
 | tail _ next ih => exact append ih (weak_source next)

theorem prepend {registry : Registry} {root : Occurrence roles} {owners : List Nat} {pool : List Output}
 {first middle last : State roles}
 (one : Weak registry root owners pool first middle)
 (tail : Counted registry root owners pool count middle last) :
 Counted registry root owners pool (count+1) first last := by
 induction tail with
 | nil _ => exact .tail (.nil _) one
 | tail _ next ih => exact .tail (ih one) next

/-- With no bound on administrative stutters, termination of the weak
progress relation still gives a projection stable under all finite futures.
This existence theorem does not compute an administrative closure. -/
theorem has_terminal (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (state : State roles) :
 ∃ last count, Counted registry root owners pool count state last ∧ Terminal registry root owners pool last ∧
 count + (project owners pool last).remaining.length ≤ (project owners pool state).remaining.length := by
 have existsPath : ∃ last count, Counted registry root owners pool count state last ∧ Terminal registry root owners pool last := by
   induction state using (GeneralRebaseWeakProgress268.wellFounded registry root owners pool).induction with
   | h state ih =>
     by_cases stuck : Terminal registry root owners pool state
     · exact ⟨state,0,.nil _,stuck⟩
     · obtain ⟨mid,first⟩ := Classical.not_forall.mp stuck
       have yes : Weak registry root owners pool state mid := Classical.byContradiction first
       obtain ⟨last,count,path,quiet⟩ := ih mid yes
       exact ⟨last,count+1,prepend yes path,quiet⟩
 obtain ⟨last,count,path,quiet⟩ := existsPath
 exact ⟨last,count,path,quiet,GeneralRebaseWeakProgress268.budget path⟩

end Yulang.GeneralRebaseWeakTerminal268
