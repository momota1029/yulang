import Yulang.GeneralNominalRebaseStore241
/-! Finite Boolean projection witness: freshness of a cell does not prevent a
live consumer from exporting its old definition as a source constraint.
This is a test of ownership hypotheses, not a Yulang program rejection. -/
namespace Yulang.GeneralNominalRebaseEscape241

def Original (source actual : Bool) : Prop :=
 ∃ cell : Bool, cell = source ∧ actual = cell

def SelfRebased (source actual : Bool) : Prop :=
 ∃ cell : Bool, cell = cell ∧ actual = cell ∧ source = source

theorem original_iff : Original source actual ↔ actual = source := by
 constructor
 · rintro ⟨cell,definition,consumer⟩
   exact consumer.trans definition
 · intro same; exact ⟨source,rfl,same⟩

theorem self_rebased (source actual : Bool) : SelfRebased source actual :=
 ⟨actual,rfl,rfl,rfl⟩

theorem lost_source_constraint : SelfRebased false true ∧ ¬ Original false true := by
 refine ⟨self_rebased _ _,?_⟩
 intro old
 have impossible := original_iff.mp old
 cases impossible

def RetainedRebase (source actual : Bool) : Prop :=
 actual = source ∧ SelfRebased source actual

theorem retained_iff : RetainedRebase source actual ↔ Original source actual := by
 rw [original_iff]
 exact ⟨And.left,fun retained => ⟨retained,self_rebased _ _⟩⟩
end Yulang.GeneralNominalRebaseEscape241
