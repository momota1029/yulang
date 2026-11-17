import Yulang.GeneralPresenceOrderedQueries247
/-! Even safe ordered blocks can change the semantic value of a raw private
address. The transported query preserves it. This is a representation-level
regression, not a claim that a source program is rejected. -/
namespace Yulang.GeneralPresenceOrderedQueryLimit247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedQueries247 GeneralPresenceOrderedDependence247
open CommonNominalFullCarrier

def old : List (Entry Nat) := [(2,.var 0)]
def fresh : List (Entry Nat) := [(2,.exactEmpty)]
def assignment : Nat → Comp model := fun _ => (.emptyRecord,Common.rowEmpty)

theorem old_safe : SafeOrder old := by
 simp [old,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem fresh_safe : SafeOrder fresh := by
 simp [fresh,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem old_valid : All model assignment (block old) := by
 intro atom member
 simp only [old,block,equations,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl
 all_goals exact subtype_refl _

theorem fresh_valid : All model (solve model fresh assignment) (block fresh) :=
 block_satisfied model (fun value => subtype_refl value) fresh fresh_safe assignment

theorem raw_private_changed : ¬ ValueEq model
 ((CompTerm.var 2).eval model assignment) ((CompTerm.var 2).eval model (solve model fresh assignment)) := by
 intro same
 have impossible : model.subTy .emptyRecord model.exactEmpty := by
   simpa [CompTerm.var,CompTerm.eval,TyTerm.eval,RowTerm.eval,solve,fresh,put,assignment] using same.1.1
 exact width_not_below_exactEmpty impossible

theorem transported_private_preserved : ValueEq model
 ((querySubst old (CompTerm.var 2)).eval model (solve model fresh assignment))
 ((CompTerm.var 2).eval model assignment) := by
 apply query_forward old fresh old_safe _ model GeneralPresenceCommonLaws245.common_laws assignment old_valid
 intro entry member
 have equal : entry = (2,TyTerm.exactEmpty) := by simpa [fresh] using member
 subst entry
 exact ⟨(2,.var 0),by simp [old],rfl⟩
end Yulang.GeneralPresenceOrderedQueryLimit247
