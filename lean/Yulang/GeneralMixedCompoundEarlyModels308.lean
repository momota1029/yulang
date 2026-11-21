import Yulang.GeneralMixedCompoundEarlyBase308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralMixedCompoundEarlyModels308
open GeneralMixedCompoundEarlyBase308 (looseSnap wideLoose)
open GeneralMixedCompoundUpperSnapshot307 (snap desc)
open GeneralMixedCompoundUpperBase307 (base)
open GeneralDictionaryJournalRefinement228Reobserve (loose exactCopy)
open GeneralDictionaryJournalRefinement228Source (snapshot)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Models Denotes Parameter Fits FitsAll)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

theorem alias (m : Assignment) (valid : GeneralNominalCommonBridge.Models base m) :
    Equivalent (m 0).1 (m 1).1 := by
  exact ⟨valid.1 (.tyLe (.var (0 : Fin 8)) (.var 1)) (by decide +kernel),
    valid.1 (.tyLe (.var (1 : Fin 8)) (.var 0)) (by decide +kernel)⟩

theorem lower (m : Assignment) (valid : GeneralNominalCommonBridge.Models base m) :
    Subtype (m 4).1 (m 2).1 :=
  valid.1 (.tyLe (.var (4 : Fin 8)) (.var 2)) (by decide +kernel)

theorem point_to_loose (m : Assignment) (valid : GeneralNominalCommonBridge.Models base m)
    {xs : List Argument} (points : FitsAll base m desc.arguments xs) :
    FitsAll base m wideLoose.arguments xs := by
  change FitsAll base m [.type ((2 : Fin 8),2),.type (2,2)] xs at points
  change FitsAll base m [.type ((4 : Fin 8),2),.type (4,2)] xs
  have widen (v : Argument) (p : Fits base m (.type ((2 : Fin 8),2)) v) :
      Fits base m (.type ((4 : Fin 8),2)) v := by
    cases v with
    | inl t => exact ⟨subtype_trans (lower m valid) p.1,p.2⟩
    | inr r => cases p
  cases points with
  | cons a tail =>
    cases tail with
    | cons b tail => cases tail; exact .cons (widen _ a) (.cons (widen _ b) .nil)

theorem old_zero (m : Assignment) (sourceModel : Models snapshot m) :
    Denotes base m (0 : Fin 8) wideLoose := by
  obtain ⟨xs,valid,eq⟩ := sourceModel.2.1 (0 : Fin 5) loose rfl
  change FitsAll snapshot.base m [.type ((4 : Fin 5),2),.type (4,2)] xs at valid
  have widen (v : Argument) (p : Fits snapshot.base m (.type ((4 : Fin 5),2)) v) :
      Fits base m (.type ((4 : Fin 8),2)) v := by
    cases v with
    | inl t => exact p
    | inr r => cases p
  refine ⟨xs,?_,eq⟩
  change FitsAll base m [.type ((4 : Fin 8),2),.type (4,2)] xs
  cases valid with
  | cons a tail =>
    cases tail with
    | cons b tail => cases tail; exact .cons (widen _ a) (.cons (widen _ b) .nil)

theorem old_one (m : Assignment) (sourceModel : Models snapshot m) :
    Denotes base m (1 : Fin 8) desc := by
  obtain ⟨xs,valid,eq⟩ := sourceModel.2.1 (1 : Fin 5) exactCopy rfl
  change FitsAll snapshot.base m [.type ((2 : Fin 5),2),.type (2,2)] xs at valid
  have widen (v : Argument) (p : Fits snapshot.base m (.type ((2 : Fin 5),2)) v) :
      Fits base m (.type ((2 : Fin 8),2)) v := by
    cases v with
    | inl t => exact p
    | inr r => cases p
  refine ⟨xs,?_,eq⟩
  change FitsAll base m [.type ((2 : Fin 8),2),.type (2,2)] xs
  cases valid with
  | cons a tail =>
    cases tail with
    | cons b tail => cases tail; exact .cons (widen _ a) (.cons (widen _ b) .nil)

theorem forced_zero (m : Assignment) (valid : GeneralNominalCommonBridge.Models base m)
    (read : Denotes base m (1 : Fin 8) desc) : Denotes base m (0 : Fin 8) desc := by
  obtain ⟨xs,fits,exactType⟩ := read
  change Equivalent (m 1).1 (nominal _ xs) at exactType
  refine ⟨xs,fits,?_⟩
  exact equivalent_trans (alias m valid) exactType

theorem equal (m : Assignment) : Models looseSnap m ↔ Models snap m := by
  constructor
  · intro h
    refine ⟨h.1,?_,h.2.2⟩
    intro slot descriptor read
    change (if slot = 0 ∨ slot = 1 then some desc else none) = some descriptor at read
    split at read
    · rename_i which
      cases Option.some.inj read
      have one : Denotes base m (1 : Fin 8) desc := h.2.1 1 desc rfl
      rcases which with rfl|rfl
      · exact forced_zero m h.1 one
      · exact one
    · cases read
  · intro h
    refine ⟨h.1,?_,h.2.2⟩
    intro slot descriptor read
    change (if slot = 0 then some wideLoose else if slot = 1 then some desc else none) = some descriptor at read
    by_cases zero : slot = 0
    · subst slot
      have eq : wideLoose = descriptor := Option.some.inj read
      subst descriptor
      obtain ⟨xs,fits,eq⟩ := h.2.1 (0 : Fin 8) desc rfl
      exact ⟨xs,point_to_loose m h.1 fits,eq⟩
    · by_cases one : slot = 1
      · subst slot
        have eq : desc = descriptor := Option.some.inj read
        subst descriptor
        exact h.2.1 (1 : Fin 8) desc rfl
      · simp [zero,one] at read

end Yulang.GeneralMixedCompoundEarlyModels308
