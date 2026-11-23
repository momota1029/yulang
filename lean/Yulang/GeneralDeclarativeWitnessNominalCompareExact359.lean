import Yulang.GeneralDeclarativeWitnessNominalExact359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNominalCompareExact359
open GeneralDeclarativeWitnessNominalSource359 (Location Route SlotRead AtSource Built Compared build compare)
open GeneralDeclarativeWitnessNominalRelation359 (Reads lower_sound)
open GeneralDeclarativeWitnessNominalExact359 (read_compile every_nested_source)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled compile hasLicense visited)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open CommonRecursiveNominalIntervals
  (Endpoint ContextWellFormed compileInContext ResultHolds)
open CommonDeclaredNominalInspection (Registry)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

def FitsSource (e : Environment) (table : Registry) (bindings : SlotRead) (context : Bool)
    (lhs rhs : Location) (a b : Route) (m : Assignment) : Prop :=
  AtSource e lhs a ∧ AtSource e rhs b ∧
  ∃ lo hi, Reads e table bindings context a lo ∧ Reads e table bindings context b hi ∧
    ContextWellFormed table context lo ∧ ContextWellFormed table context hi ∧
    ContextDerives table m context lo hi

theorem builds_exact_source {e table slots context loc route endpoint}
    (source : AtSource e loc route) (shape : Reads e table slots context route endpoint) :
    ∃ built : Built e table slots context loc route,
      build e table slots context loc route = some built ∧ built.endpoint = endpoint := by
  have reads := read_compile shape
  refine ⟨⟨source,endpoint,reads⟩,?_,rfl⟩
  unfold build
  unfold AtSource at source
  rw [dite_eq_left source]
  split
  · rename_i none
    rw [reads] at none
    cases none
  · rename_i found read
    have eq : found = endpoint := Option.some.inj (read.symm.trans reads)
    subst found
    rfl

theorem scoped_compares_exact {e table slots ctx lhs rhs a b} {m : Assignment} :
    (∃ checked : Compared e table slots ctx lhs rhs a b,
      compare e table slots ctx lhs rhs a b = some checked ∧
        ∀ atom ∈ checked.run.rows,atom.Holds model m) ↔ FitsSource e table slots ctx lhs rhs a b m := by
  constructor
  · rintro ⟨c,_,fits⟩
    have sem := (compiled_full_exact table m ctx c.first.endpoint c.last.endpoint).mp
      ⟨c.run.rows,c.run.exact,fits⟩
    exact ⟨c.first.source,c.last.source,c.first.endpoint,c.last.endpoint,
      lower_sound c.first.lowered,lower_sound c.last.lowered,sem⟩
  · rintro ⟨actualL,actualR,lo,hi,pathL,pathR,formL,formR,meaning⟩
    obtain ⟨first,foundL,shapeL⟩ := builds_exact_source actualL pathL
    obtain ⟨last,foundR,shapeR⟩ := builds_exact_source actualR pathR
    have covered : (visited first.endpoint ++ visited last.endpoint).all (hasLicense e table) = true := by
      rw [shapeL,shapeR,List.all_eq_true]
      intro site found
      rcases List.mem_append.mp found with l|r
      · exact every_nested_source pathL _ l
      · exact every_nested_source pathR _ r
    have compiled : ResultHolds (fun atom => atom.Holds model m)
        (compileInContext table ctx first.endpoint last.endpoint) := by
      rw [shapeL,shapeR]
      exact (compiled_full_exact table m ctx lo hi).mpr ⟨formL,formR,meaning⟩
    obtain ⟨rows,emitted,thanks⟩ := compiled
    have ran : ∃ c : Compiled e table ctx first.endpoint last.endpoint,
        compile e table ctx first.endpoint last.endpoint = some c ∧ c.rows = rows := by
      unfold compile
      rw [dite_eq_left covered]
      split
      · rename_i actual hit
        have same : actual = rows := Option.some.inj (hit.symm.trans emitted)
        subst actual
        exact ⟨_,rfl,rfl⟩
      · rename_i absent
        rw [emitted] at absent
        cases absent
    obtain ⟨c,ran,cRows⟩ := ran
    refine ⟨⟨first,last,c⟩,?_,fun a here => thanks a (cRows ▸ here)⟩
    simp [GeneralDeclarativeWitnessNominalSource359.compare,foundL,foundR,ran,bind,Option.bind,pure]

end Yulang.GeneralDeclarativeWitnessNominalCompareExact359
