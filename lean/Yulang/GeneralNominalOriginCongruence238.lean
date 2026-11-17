import Yulang.GeneralNominalRawCongruence238
import Yulang.GeneralNominalOriginTerms
set_option backward.isDefEq.respectTransparency false
/-! Observational origins respect pointwise full nominal equivalence. Source
observations may change syntactically; existential witnesses are transported. -/
namespace Yulang.GeneralNominalOriginCongruence238
open GeneralNominalAssignmentCongruence238 (Same)
open GeneralNominalRawCongruence238 (equiv_trans equiv_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
variable {first last : Assignment}

theorem observes (same : Same first last) (seen : Observes first origin value) :
 ∃ other, Observes last origin other ∧ Equivalent value other := by
 induction seen with
 | source n => exact ⟨_,.source n,(same n).1⟩
 | nominal parent equal found ih =>
   obtain ⟨other,seen,same⟩ := ih
   exact ⟨_,.nominal seen (equiv_trans ⟨same.2,same.1⟩ equal) found,⟨subtype_refl _,subtype_refl _⟩⟩
 | structural parent length equal found ih =>
   obtain ⟨other,seen,same⟩ := ih
   exact ⟨_,.structural seen length (equiv_trans ⟨same.2,same.1⟩ equal) found,⟨subtype_refl _,subtype_refl _⟩⟩

theorem inhabited_iff (same : Same first last) (origin : Origin) :
 (∃ value, Observes first origin value) ↔ ∃ value, Observes last origin value := by
 constructor
 · rintro ⟨value,seen⟩; obtain ⟨other,seen,_⟩ := observes same seen; exact ⟨other,seen⟩
 · rintro ⟨value,seen⟩; obtain ⟨other,seen,_⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen; exact ⟨other,seen⟩

theorem test_iff (same : Equivalent x y) (test : Test) : test.Holds x ↔ test.Holds y := by
 cases test with
 | scalar scalar => exact equiv_iff same ⟨subtype_refl _,subtype_refl _⟩
 | structural shape =>
   apply exists_congr; intro values
   exact and_congr Iff.rfl (equiv_iff same ⟨subtype_refl _,subtype_refl _⟩)
 | nominal name count =>
   apply exists_congr; intro values
   exact and_congr Iff.rfl (equiv_iff same ⟨subtype_refl _,subtype_refl _⟩)

theorem head (same : Same first last) (valid : GeneralNominalOriginTerms.Head first origin test) :
 GeneralNominalOriginTerms.Head last origin test := by
 refine ⟨(inhabited_iff same origin).mp valid.1,?_⟩
 intro value seen
 obtain ⟨other,observed,equal⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) seen
 exact (test_iff equal test).mpr (valid.2 other observed)

theorem head_iff (same : Same first last) (origin : Origin) (test : Test) :
 GeneralNominalOriginTerms.Head first origin test ↔ GeneralNominalOriginTerms.Head last origin test :=
 ⟨head same,head (GeneralNominalAssignmentCongruence238.symm same)⟩

theorem shared (same : Same first last) (valid : GeneralNominalOriginTerms.Same first a b) :
 GeneralNominalOriginTerms.Same last a b := by
 refine ⟨(inhabited_iff same a).mp valid.1,(inhabited_iff same b).mp valid.2.1,?_⟩
 intro x y one two
 obtain ⟨oldx,oldone,xsame⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) one
 obtain ⟨oldy,oldtwo,ysame⟩ := observes (GeneralNominalAssignmentCongruence238.symm same) two
 exact equiv_trans xsame (equiv_trans (valid.2.2 oldx oldy oldone oldtwo) ⟨ysame.2,ysame.1⟩)

theorem shared_iff (same : Same first last) (a b : Origin) :
 GeneralNominalOriginTerms.Same first a b ↔ GeneralNominalOriginTerms.Same last a b :=
 ⟨shared same,shared (GeneralNominalAssignmentCongruence238.symm same)⟩

theorem expression_iff (same : Same first last) (expression : GeneralNominalOriginTerms.Expr Origin) (origin : Origin) :
 GeneralNominalOriginTerms.Holds first expression origin ↔ GeneralNominalOriginTerms.Holds last expression origin := by
 induction expression generalizing origin with
 | leaf source => exact shared_iff same origin source
 | node test children ih =>
   exact and_congr (head_iff same origin test) (forall_congr' fun index => ih index _)
end Yulang.GeneralNominalOriginCongruence238
