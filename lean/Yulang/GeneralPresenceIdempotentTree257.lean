import Yulang.GeneralPresenceCommonLaws245
import Yulang.GeneralPresenceSnapshotGrowth251
namespace Yulang.GeneralPresenceIdempotentTree257
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def join (a b : TyTerm Nat) : TyTerm Nat := if a = b then a else .union a b
def meet (a b : TyTerm Nat) : TyTerm Nat := if a = b then a else .inter a b

/-- Structural duplicate reduction, not a distributive or complete normal form.
Rows remain literal; no public names are identified by semantic equivalence. -/
def reduce : TyTerm Nat → TyTerm Nat
 | .union a b => join (reduce a) (reduce b)
 | .inter a b => meet (reduce a) (reduce b)
 | .pair a b => .pair (reduce a) (reduce b)
 | .record l a b => .record l (reduce a) (reduce b)
 | .recordDefault l a b => .recordDefault l (reduce a) (reduce b)
 | .required l a => .required l (reduce a)
 | .variant l a => .variant l (reduce a)
 | .arrow a incoming b outgoing => .arrow (reduce a) incoming (reduce b) outgoing
 | term => term

theorem meet_self (value : Ty) : Equivalent (.inter value value) value :=
 ⟨((common_inter_is_meet value value (.inter value value)).mp (subtype_refl _)).1,
   (common_inter_is_meet value value value).mpr ⟨subtype_refl _,subtype_refl _⟩⟩

theorem join_exact (a b : TyTerm Nat) (assignment : Assignment) :
 Equivalent ((join a b).eval model assignment) ((TyTerm.union a b).eval model assignment) := by
 by_cases same : a = b
 · subst b; simp only [join,ite_true]
   have idem := GeneralPresenceSnapshotGrowth251.union_self (a.eval model assignment)
   exact ⟨idem.2,idem.1⟩
 · simp only [join,same,ite_false]
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem meet_exact (a b : TyTerm Nat) (assignment : Assignment) :
 Equivalent ((meet a b).eval model assignment) ((TyTerm.inter a b).eval model assignment) := by
 by_cases same : a = b
 · subst b; simp only [meet,ite_true]
   have idem := meet_self (a.eval model assignment)
   exact ⟨idem.2,idem.1⟩
 · simp only [meet,same,ite_false]
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem equivalent (term : TyTerm Nat) (assignment : Assignment) :
 Equivalent ((reduce term).eval model assignment) (term.eval model assignment) := by
 have laws := GeneralPresenceCommonLaws245.common_laws
 induction term with
 | union a b ihA ihB =>
   have first := join_exact (reduce a) (reduce b) assignment
   have last := laws.union_congr _ _ _ _ ihA ihB
   exact ⟨subtype_trans first.1 last.1,subtype_trans last.2 first.2⟩
 | inter a b ihA ihB =>
   have first := meet_exact (reduce a) (reduce b) assignment
   have last := laws.inter_congr _ _ _ _ ihA ihB
   exact ⟨subtype_trans first.1 last.1,subtype_trans last.2 first.2⟩
 | pair a b ihA ihB => exact laws.pair_congr _ _ _ _ ihA ihB
 | record l a b ihA ihB => exact laws.record_congr _ _ _ _ _ ihA ihB
 | recordDefault l a b ihA ihB => exact laws.recordDefault_congr _ _ _ _ _ ihA ihB
 | required l a ih => exact laws.required_congr _ _ _ ih
 | variant l a ih => exact laws.variant_congr _ _ _ ih
 | arrow a incoming b outgoing ihA ihB => exact laws.arrow_congr _ _ _ _ _ _ ihA ihB
 | var | base | bottom | top | emptyRecord | exactEmpty => exact ⟨subtype_refl _,subtype_refl _⟩

def atom : PresenceNormalForm.Atom Nat → PresenceNormalForm.Atom Nat
 | .tyLe a b => .tyLe (reduce a) (reduce b)
 | .rowLe a b => .rowLe a b

theorem atom_exact (value : PresenceNormalForm.Atom Nat) (assignment : Assignment) :
 (atom value).Holds model assignment ↔ value.Holds model assignment := by
 cases value with
 | tyLe a b => exact GeneralPresenceModelCongruence245.subTy_iff GeneralPresenceCommonLaws245.common_laws (equivalent a assignment) (equivalent b assignment)
 | rowLe => exact Iff.rfl

theorem all_exact (values : List (PresenceNormalForm.Atom Nat)) (assignment : Assignment) :
 PresenceNormalForm.All model assignment (values.map atom) ↔ PresenceNormalForm.All model assignment values := by
 constructor
 · intro valid value member
   exact (atom_exact value assignment).mp (valid _ (List.mem_map.mpr ⟨value,member,rfl⟩))
 · intro valid value member
   obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
   exact (atom_exact original assignment).mpr (valid original present)
end Yulang.GeneralPresenceIdempotentTree257
