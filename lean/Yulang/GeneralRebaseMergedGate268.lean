import Yulang.GeneralRebaseRawK2Probe268
import Yulang.GeneralRebaseExecutableAlias267
import Yulang.GeneralNominalVersionedMergedConflict232

namespace Yulang.GeneralRebaseMergedGate268
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseExecutableAlias267 (aliased aliased_exact)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebasePartialBool268 (Reflect)

def member (state : State roles) (focus : Occurrence roles) : Bool :=
 state.core.erased.current.aliases.any fun pair =>
  !(pair.1 == pair.2) && aliased state.core.erased.current focus.identity pair.1

theorem member_exact (state : State roles) (focus : Occurrence roles) :
 member state focus = true ↔ GeneralNominalVersionedMergedConflict232.Old.MergedClass state.legacy focus := by
 simp only [member,List.any_eq_true,Bool.and_eq_true,Bool.not_eq_true',←Bool.not_eq_true,beq_iff_eq,aliased_exact,
  GeneralNominalVersionedMergedConflict232.Old.MergedClass,GeneralNominalCenteredHeadAllocMergedConflict.MergedClass]
 constructor
 · rintro ⟨⟨a,b⟩,listed,diff,aliased⟩
   exact ⟨a,b,listed,diff,aliased⟩
 · rintro ⟨a,b,listed,diff,aliased⟩
   exact ⟨(a,b),listed,diff,aliased⟩

def probe (state : State roles) (focus : Occurrence roles) : Option Bool :=
 if member state focus then none else some false

theorem probe_sound (registry : GeneralDeclarations.Registry) (state : State roles) (focus : Occurrence roles) :
 Reflect ((Boundary roles).MergedOutputConflict registry state focus) (probe state focus) := by
 unfold probe
 split
 · trivial
 · rename_i no
   intro actual
   have present := (member_exact state focus).mpr actual.1
   exact no present

end Yulang.GeneralRebaseMergedGate268
