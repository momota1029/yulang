import Yulang.GeneralRebaseDepthRaw284Bridge285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseDepthGroundModels285
open GeneralDictionaryOutputDepth252 (snapshot atoms foo base F S P scalar_fixed foo_fixed plan initial)
open GeneralDictionaryOutputDepthInstall252 (installed output_forced)
open GeneralRebaseDepthPublic285 (exact_same_assignment project)
open GeneralRebaseDepthReads285 (actualEquation)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_trans)

def InitialTypeCheck (m : Assignment) : Prop :=
 Equivalent (m 0).1 S ∧ Equivalent (m 1).1 S ∧ Equivalent (m 2).1 F

def FinalTypeCheck (m : Assignment) : Prop :=
 InitialTypeCheck m ∧ Equivalent (m 3).1 P

theorem source_inputs (m : Assignment) :
    GeneralNominalState.Models snapshot m ↔ InitialTypeCheck m := by
  constructor
  · intro held
    refine ⟨scalar_fixed m held,⟨?_,?_⟩,foo_fixed m held⟩
    · exact held.1.1 (.tyLe (.var 1) (.base .int)) (by simp [atoms,GeneralSourceState.equationAtoms])
    · exact held.1.1 (.tyLe (.base .int) (.var 1)) (by simp [atoms,GeneralSourceState.equationAtoms])
  · rintro ⟨zero,one,two⟩
    refine ⟨⟨?_,(by intro _ _ h; cases h),(by intro _ h; cases h)⟩,?_,(by intro _ h; cases h)⟩
    · intro atom member
      simp only [atoms,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
        GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact zero.1
      · exact zero.2
      · exact one.1
      · exact one.2
    · intro slot d found
      change (if slot = 2 then some foo else none) = some d at found
      split at found
      · rename_i same; subst slot; cases Option.some.inj found
        exact ⟨[.inl S],.cons zero .nil,two⟩
      · cases found

theorem close_ground (m : Assignment) (input : Equivalent (m 2).1 F) :
    Equivalent (GeneralRebaseDepthReads285.valueFromInput m) P := by
  have first := GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons input .nil)
  exact GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons first .nil)

theorem final_check (m : Assignment) : Models installed m ↔ FinalTypeCheck m := by
  constructor
  · intro held
    exact ⟨(source_inputs m).mp ((exact_same_assignment m).mp held).1,output_forced m held⟩
  · intro checks
    have close := close_ground m checks.1.2.2
    apply (exact_same_assignment m).mpr
    refine ⟨(source_inputs m).mpr checks.1,?_⟩
    change Equivalent (m 3).1 (GeneralRebaseDepthReads285.valueFromInput m)
    exact ⟨subtype_trans checks.2.1 close.2,subtype_trans close.1 checks.2.2⟩

/-- No row coordinate is semantically read by this raw fixture. The row
values remain part of the surrounding assignment and are not rewritten. -/
theorem no_row_requirement (a b : Assignment) (types : ∀ n ≤ 3, (a n).1 = (b n).1) :
    Models installed a ↔ Models installed b := by
  rw [final_check a,final_check b]
  simp only [FinalTypeCheck,InitialTypeCheck,types 0 (by decide),types 1 (by decide),
    types 2 (by decide),types 3 (by decide)]

theorem canonical_check (a : Assignment) :
    Models installed (GeneralRebaseDepthPublic285.inflate (project a) (fun n => (a n).2)) ↔
    InitialTypeCheck a :=
 (GeneralRebaseDepthPublic285.canonical_models a).trans (source_inputs a)

end Yulang.GeneralRebaseDepthGroundModels285
