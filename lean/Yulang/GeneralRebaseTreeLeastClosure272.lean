import Yulang.GeneralRebaseTreeCompileMonotone272

namespace Yulang.GeneralRebaseTreeLeastClosure272
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseTreeInterpreter272 (Certified Source)
open GeneralRebaseTreeSchema272 (enrich enrich_sound runPlans rounds)
open GeneralRebaseTreeSchemaClosure272 (Stable close close_sound close_stable preserved_by_close)
open GeneralRebaseTreeCompileMonotone272 (Extends extends_trans enrich_mono)
open GeneralRebaseTreeSchemaProgress272 (next_known)

theorem antisymm {a b : Source} (one : Extends a b) (two : Extends b a) : a = b := by
 funext id
 cases found : a id with
 | some value => exact (one id value found).symm
 | none =>
   cases other : b id with
   | none => rfl
   | some value =>
     have impossible := two id value other
     rw [found] at impossible
     cases impossible

theorem pass_mono (plans : List (Plan roles)) (m : Assignment) (a b : Source)
 (left : Certified m a) (right : Certified m b) (pre : Extends a b)
 (checked : ∀ p ∈ plans, GeneralNominalVersionedPlans231.Outputs p m) :
 Extends (runPlans a plans) (runPlans b plans) := by
 induction plans generalizing a b with
 | nil => exact pre
 | cons p ps ih =>
   have h := checked p List.mem_cons_self
   exact ih (enrich a p) (enrich b p) (enrich_sound a p m left h) (enrich_sound b p m right h)
      (enrich_mono m a b pre left right p h) (fun p found => checked p (List.mem_cons_of_mem _ found))

theorem rounds_below_fixed (state : State roles) (m : Assignment) (valid : Models state m)
 (a upper : Source) (first : Certified m a) (last : Certified m upper) (under : Extends a upper)
 (fixed : Stable state upper) (n : Nat) : Extends (rounds state n a) upper := by
 induction n generalizing a with
 | zero => exact under
 | succ n ih =>
   have supported : ∀ p ∈ state.plans, GeneralNominalVersionedPlans231.Outputs p m :=
     fun p found => (valid.2.1 p found).2.2
   have one := pass_mono state.plans m a upper first last under supported
   rw [fixed] at one
   exact ih (runPlans a state.plans)
     (GeneralRebaseTreeSchema272.runPlans_sound a state.plans m first supported) one

theorem least (state : State roles) (m : Assignment) (valid : Models state m)
 (seed upper : Source) (seedCert : Certified m seed) (upperCert : Certified m upper)
 (under : Extends seed upper) (fixed : Stable state upper) :
 Extends (close state seed) upper :=
 rounds_below_fixed state m valid seed upper seedCert upperCert under fixed _

theorem fixed_iff_each (plans : List (Plan roles)) (src : Source) :
 runPlans src plans = src ↔ ∀ p ∈ plans, enrich src p = src := by
 induction plans with
 | nil => exact ⟨fun _ _ impossible => False.elim (List.not_mem_nil impossible),fun _ => rfl⟩
 | cons p ps ih =>
   constructor
   · intro complete
     have pre : Extends src (enrich src p) := fun id t h =>
       GeneralRebaseTreeSchema272.enrich_preserves_source src p id t h
     have post : Extends (enrich src p) (runPlans src (p::ps)) :=
       fun id t h => next_known ps (enrich src p) id t h
     rw [complete] at post
     have noNew := antisymm post pre
     have tail : runPlans src ps = src := by
       change runPlans (enrich src p) ps = src at complete
       rw [noNew] at complete
       exact complete
     intro q member
     rcases List.mem_cons.mp member with rfl | h
     · exact noNew
     · exact ih.mp tail q h
   · intro each
     change runPlans (enrich src p) ps = src
     rw [each p List.mem_cons_self]
     exact ih.mpr (fun q present => each q (List.mem_cons_of_mem _ present))

theorem order_independent (a b : State roles) (m : Assignment) (first : Models a m) (last : Models b m)
 (samePlans : a.plans.Perm b.plans) (seed : Source) (known : Certified m seed) :
 close a seed = close b seed := by
 have fixedA := close_stable a seed
 have fixedB := close_stable b seed
 have aForB : Stable b (close a seed) := (fixed_iff_each b.plans _).mpr
   (fun p member => (fixed_iff_each a.plans _).mp fixedA p (samePlans.mem_iff.mpr member))
 have bForA : Stable a (close b seed) := (fixed_iff_each a.plans _).mpr
   (fun p member => (fixed_iff_each b.plans _).mp fixedB p (samePlans.mem_iff.mp member))
 exact antisymm
   (least a m first seed _ known (close_sound b m last seed known)
      (preserved_by_close b seed) bForA)
   (least b m last seed _ known (close_sound a m first seed known)
      (preserved_by_close a seed) aForB)

end Yulang.GeneralRebaseTreeLeastClosure272
