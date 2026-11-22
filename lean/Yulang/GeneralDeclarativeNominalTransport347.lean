import Yulang.GeneralDeclarativeNominalIntervals347
import Yulang.GeneralNominalProjections

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNominalTransport347
open GeneralNominalState (State Models Parameter)
open GeneralNominalRefinements (Refines renameParameter renameDescriptor)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeNominalIntervals347 (Named encode fits FitList observes)
open CommonNominalFullCarrier (Argument Ty Subtype Equivalent nominal)

abbrev lookup := GeneralDeclarativeNominalIntervals347.read

theorem encode_refinement {s t : State} (grow : Refines s t) (p : Parameter s.base.slots) :
    encode t.base (renameParameter grow.base.embed p) = encode s.base p := by
  cases p with
  | type bounds =>
    obtain ⟨l,u⟩ := bounds
    simp [renameParameter,encode,grow.base.source]
  | row bounds =>
    obtain ⟨l,u⟩ := bounds
    simp [renameParameter,encode,grow.base.rowSource]

/-- A checked ordinary slot refinement may remap physical indices but
cannot change any of the actual source names in a nominal read.
A descriptor revision is deliberately not such a refinement. -/
theorem stable_refinement {s t : State} (grow : Refines s t) {root key : Nat} {xs : List Named}
    (seen : lookup s root = some (key,xs)) : lookup t root = some (key,xs) := by
  obtain ⟨i,d,slot,entry,rfl,rfl⟩ := GeneralDeclarativeNominalIntervals347.read_exact.mp seen
  refine GeneralDeclarativeNominalIntervals347.read_exact.mpr
    ⟨grow.base.embed i,renameDescriptor grow.base.embed d,?_,grow.nominals i d entry,rfl,?_⟩
  · exact (sourceSlot_exact ..).mpr ((grow.base.source i).trans ((sourceSlot_exact ..).mp slot))
  · simp [renameDescriptor,List.map_map,Function.comp_def,encode_refinement grow]

theorem fit_at {m : Assignment} {xs : List Named} {vs : List Argument} {i : Nat} {x : Named}
    (fit : FitList m xs vs) (there : xs[i]? = some x) :
    ∃ v, vs[i]? = some v ∧ fits m x v := by
  induction fit generalizing i with
  | nil => cases i <;> simp at there
  | @cons a v as vs head tail ih =>
    cases i with
    | zero =>
      have same : a = x := Option.some.inj there
      subst x
      exact ⟨v,rfl,head⟩
    | succ i =>
      obtain ⟨actual,eq,hit⟩ := ih (i := i) there
      exact ⟨actual,eq,hit⟩

/-- A typed position in the actual raw nominal descriptor really
projects one invariant argument with these bounds in every raw model.
The argument is witnessed by the root, not chosen from either endpoint. -/
theorem type_projection {s : State} {root key i lo hi : Nat} {xs : List Named}
    (seen : lookup s root = some (key,xs)) (there : xs[i]? = some (.type lo hi))
    (m : Assignment) (model : Models s m) :
    ∃ actual : Ty, GeneralNominalProjections.Observes m (.argument (.source root) key i) (.inl actual) ∧
      Subtype (m lo).1 actual ∧ Subtype actual (m hi).1 := by
  obtain ⟨values,fit,isRoot⟩ := observes seen m model
  obtain ⟨value,slot,atType⟩ := fit_at fit there
  cases value with
  | inl actual => exact ⟨actual,.argument (.source root) isRoot slot,atType⟩
  | inr _ => exact False.elim atType

theorem row_projection {s : State} {root key i lo hi : Nat} {xs : List Named}
    (seen : lookup s root = some (key,xs)) (there : xs[i]? = some (.row lo hi))
    (m : Assignment) (model : Models s m) :
    ∃ actual, GeneralNominalProjections.Observes m (.argument (.source root) key i) (.inr actual) ∧
      Common.rowLe (m lo).2 actual ∧ Common.rowLe actual (m hi).2 := by
  obtain ⟨values,fit,isRoot⟩ := observes seen m model
  obtain ⟨value,slot,atRow⟩ := fit_at fit there
  cases value with
  | inl _ => exact False.elim atRow
  | inr actual => exact ⟨actual,.argument (.source root) isRoot slot,atRow⟩

end Yulang.GeneralDeclarativeNominalTransport347
