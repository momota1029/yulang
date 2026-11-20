import Yulang.GeneralMixedFullControlUnlabelled306
import Yulang.GeneralFiniteBisimRefinement306

namespace Yulang.GeneralMixedFullControlMinimal306
open GeneralMixedFullControlCode306
open GeneralMixedFullControlUnlabelled306
open GeneralFiniteBisimRefinement306 (Strong rounds retains)
open GeneralMixedControlMask306 (rank)

theorem separated (x y : ControlClass) :
    rounds classTargets 3 x y = true ↔ x = y := by
  cases x <;> cases y <;> decide

def CodeBisim (rel : Code → Code → Prop) := Strong targets rel

theorem projected_bisim {rel : Code → Code → Prop} (b : CodeBisim rel) :
    Strong classTargets (fun a c => ∃ x y, rel x y ∧ classify x = a ∧ classify y = c) := by
  rintro a c ⟨x,y,same,rfl,rfl⟩
  have act := b x y same
  constructor
  · intro g records
    obtain ⟨dest,yes,tag⟩ := (class_exact x g).mpr records
    obtain ⟨other,listed,related⟩ := act.1 dest (List.mem_filter.mpr ⟨all_codes dest,yes⟩)
    exact ⟨classify other,(class_exact y _).mp ⟨other,(List.mem_filter.mp listed).2,rfl⟩,
      dest,other,related,tag,rfl⟩
  · intro g records
    obtain ⟨dest,yes,tag⟩ := (class_exact y g).mpr records
    obtain ⟨other,listed,related⟩ := act.2 dest (List.mem_filter.mpr ⟨all_codes dest,yes⟩)
    exact ⟨classify other,(class_exact x _).mp ⟨other,(List.mem_filter.mp listed).2,rfl⟩,
      other,dest,related,rfl,tag⟩

theorem each_bisim_respects_classes {rel : Code → Code → Prop} (b : CodeBisim rel)
    (x y : Code) (h : rel x y) : classify x = classify y :=
  (separated _ _).mp (retains (projected_bisim b) 3 _ _ ⟨x,y,h,rfl,rfl⟩)

theorem classes_bisim : CodeBisim (fun x y => classify x = classify y) := by
  intro x y eq
  constructor
  · intro a listed
    have member := (class_exact x _).mp ⟨a,(List.mem_filter.mp listed).2,rfl⟩
    rw [eq] at member
    obtain ⟨b,edge,tag⟩ := (class_exact y _).mpr member
    exact ⟨b,List.mem_filter.mpr ⟨all_codes b,edge⟩,tag.symm⟩
  · intro b listed
    have member := (class_exact y _).mp ⟨b,(List.mem_filter.mp listed).2,rfl⟩
    rw [← eq] at member
    obtain ⟨a,edge,tag⟩ := (class_exact x _).mpr member
    exact ⟨a,List.mem_filter.mpr ⟨all_codes a,edge⟩,tag⟩

def obligations (x : Code) : Nat := (if x.installed then 0 else 1) + rank x.scalars

theorem counting_is_not_exact :
    ∃ x y : Code, obligations x = obligations y ∧
      (∃ x', moves x x' = true ∧ classify x' = .halted) ∧
      ¬ (∃ y', moves y y' = true ∧ classify y' = .halted) := by
  let postTwo : Code := ⟨true,⟨false,false⟩⟩
  let preSplit : Code := ⟨false,⟨true,false⟩⟩
  refine ⟨postTwo,preSplit,rfl,?_,?_⟩
  · exact (class_exact postTwo .halted).mpr (by decide +kernel)
  · intro found
    have cannot : ControlClass.halted ∉ classTargets (classify preSplit) := by decide +kernel
    exact cannot ((class_exact preSplit .halted).mp found)

end Yulang.GeneralMixedFullControlMinimal306
