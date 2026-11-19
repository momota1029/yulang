import Yulang.GeneralRebaseScalarSnapshot271

namespace Yulang.GeneralRebaseJournalMeaning271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Head Edge Path Cyclic RootCycle)
open GeneralNominalRecursiveInspection (Origin Test)
open GeneralSourceDictionaries (Occurrence)

def SameModels (a b : State roles) : Prop := ∀ m, Models a m ↔ Models b m

theorem equality {a b : State roles} (agree : SameModels a b) (x y : Origin) :
 Equal a x y ↔ Equal b x y :=
 ⟨fun held m valid => held m ((agree m).mpr valid),fun held m valid => held m ((agree m).mp valid)⟩

theorem test {a b : State roles} (agree : SameModels a b) (x : Origin) (check : Test) :
 Head a x check ↔ Head b x check :=
 ⟨fun held m valid => held m ((agree m).mpr valid),fun held m valid => held m ((agree m).mp valid)⟩

theorem edge {a b : State roles} (agree : SameModels a b) (x y : Origin) :
 Edge a x y ↔ Edge b x y := by
 have carry (a b : State roles) (agreement : SameModels a b) : Edge a x y → Edge b x y := by
   rintro ⟨p,t,i,h,left,right⟩
   exact ⟨p,t,i,(test agreement ..).mp h,(equality agreement ..).mp left,(equality agreement ..).mp right⟩
 exact ⟨carry a b agree,carry b a (fun m => (agree m).symm)⟩

theorem path {a b : State roles} (agree : SameModels a b) (x y : Origin) :
 Path a x y ↔ Path b x y := by
 have carry (a b : State roles) (agreement : SameModels a b) (x y : Origin) (h : Path a x y) : Path b x y := by
   induction h with
   | nil => exact .nil _
   | cons s _ ih => exact .cons ((edge agreement ..).mp s) ih
 exact ⟨carry a b agree x y,carry b a (fun m => (agree m).symm) x y⟩

theorem cyclic {a b : State roles} (agree : SameModels a b) (x : Origin) :
 Cyclic a x ↔ Cyclic b x := by
 have move (a b : State roles) (agreement : SameModels a b) : Cyclic a x → Cyclic b x := by
   rintro ⟨⟨endSlot,arrive,back⟩,m,valid⟩
   exact ⟨⟨endSlot,(edge agreement ..).mp arrive,(path agreement ..).mp back⟩,m,(agreement m).mp valid⟩
 exact ⟨move a b agree,move b a (fun m => (agree m).symm)⟩

theorem root {a b : State roles} (agree : SameModels a b) (sites : a.core.sites = b.core.sites)
 (focus : Occurrence roles) :
 RootCycle a focus ↔ RootCycle b focus := by
 have move (a b : State roles) (agreement : SameModels a b) (list : a.core.sites = b.core.sites) :
   RootCycle a focus → RootCycle b focus := by
   intro actual
   rcases actual with ⟨i,cyc⟩ | ⟨s,member,same,i,cyc⟩
   · exact Or.inl ⟨i,(cyclic agreement _).mp cyc⟩
   · exact Or.inr ⟨s,list ▸ member,same,i,(cyclic agreement _).mp cyc⟩
 exact ⟨move a b agree sites,move b a (fun m => (agree m).symm) sites.symm⟩

end Yulang.GeneralRebaseJournalMeaning271
