import Yulang.GeneralDeclarativeWitnessTypedOverlap354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedConservative354
open GeneralDeclarativeWitnessTypedOutput354 (Typed Batch ordinary typedRows)
open GeneralDeclarativeWitnessTypedPacket354 (Run)
open GeneralDeclarativeWitnessCompiler350 (fixedBatch)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDictionaryAssociatedProvenance (lookup)

theorem ordinary_recovered {p c names outs} (b : Batch p c names outs)
    (notTyped : typedRows b.trace = []) :
    collect (one c.registry c.interp c.decl c.demand names) outs = some (ordinary b.trace) := by
  induction b with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | nominal src => cases notTyped
    | ordinary e old target =>
      have h : typedRows rest.trace = [] := notTyped
      simp only [collect,old,ih h,Option.bind_eq_bind,Option.bind_some,Batch.trace,ordinary,
        List.filterMap_cons,GeneralDeclarativeWitnessTypedOutput354.Item.write,List.singleton_append,Option.pure_def]

theorem no_ordinary_semantics_changed {p w} (r : Run p w)
    (h : typedRows r.writes.trace = []) :
    fixedBatch r.source.ctx r.ports = some (ordinary r.writes.trace) :=
  ordinary_recovered r.writes h

theorem no_default_as_typed {p c names out} (t : Typed p c names out) (rhs : Roles.Term) :
    lookup c.registry.roles c.decl out.name ≠ some (.default c.decl.role out.name rhs) := by
  intro alt
  have clash := Option.some.inj (t.found.symm.trans alt)
  cases clash

end Yulang.GeneralDeclarativeWitnessTypedConservative354
