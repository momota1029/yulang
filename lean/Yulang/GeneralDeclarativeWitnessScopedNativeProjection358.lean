import Yulang.GeneralDeclarativeWitnessSourceChain358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessScopedNativeProjection358
open GeneralDeclarativeWitnessAuthoredProjection358 (Recipe Projected BoundsIn original_nonpoint_projection)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives compiled_full_exact)
open GeneralDeclarativeWitnessSparseIntervals357 (compile Compiled)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open CommonRecursiveNominalIntervals (Endpoint ResultHolds result_some)
open Core.PresenceGeneration (TyTerm)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)

def line (name : Nat) : Endpoint Nat := .ordinary (.var name)
def observed (tag slot : Nat) : Endpoint Nat := .ordinary (.variant tag (.var slot))

theorem compiled_ordinary (context : Bool) (lhs rhs : TyTerm Nat) :
    CommonRecursiveNominalIntervals.compileInContext [] context (.ordinary lhs) (.ordinary rhs) =
      some [PresenceNormalForm.Atom.tyLe lhs rhs] := by
  unfold CommonRecursiveNominalIntervals.compileInContext
  have both : (CommonRecursiveNominalIntervals.admitContext [] context (.ordinary lhs) &&
      CommonRecursiveNominalIntervals.admitContext [] context (.ordinary rhs)) = true := by
    simp only [CommonRecursiveNominalIntervals.admitContext.eq_def,Bool.and_self]
  rw [ite_eq_left both,CommonRecursiveNominalIntervals.inspectContext]

theorem exact_component (e : Environment) (context : Bool) (lhs rhs : TyTerm Nat) :
    (compile e [] context (.ordinary lhs) (.ordinary rhs)).map Compiled.rows =
      some [PresenceNormalForm.Atom.tyLe lhs rhs] := by
  unfold compile
  have clean : ((GeneralDeclarativeWitnessSparseIntervals357.visited (.ordinary lhs) ++
      GeneralDeclarativeWitnessSparseIntervals357.visited (.ordinary rhs)).all
        (GeneralDeclarativeWitnessSparseIntervals357.hasLicense e [])) = true := by
    simp [GeneralDeclarativeWitnessSparseIntervals357.visited]
  rw [dite_eq_left clean]
  split
  · rename_i rows hit
    have known := Option.some.inj (hit.symm.trans (compiled_ordinary context lhs rhs))
    exact congrArg some known
  · rename_i impossible
    have bad := (compiled_ordinary context lhs rhs).symm.trans impossible
    cases bad

theorem check_projection_context {a s r} (supported : Projected a s r)
    (m : Assignment) (fit : Models s m) (context : Bool) :
    ContextDerives [] m context (line r.outer.lower) (observed r.tag r.inner.lower) ∧
    ContextDerives [] m context (observed r.tag r.inner.lower) (line r.outer.lower) ∧
    ContextDerives [] m context (line r.outer.center) (observed r.tag r.inner.center) ∧
    ContextDerives [] m context (observed r.tag r.inner.center) (line r.outer.center) ∧
    ContextDerives [] m context (line r.outer.upper) (observed r.tag r.inner.upper) ∧
    ContextDerives [] m context (observed r.tag r.inner.upper) (line r.outer.upper) := by
  have arrived := original_nonpoint_projection supported m fit
  have fromConstraint (lhs rhs : TyTerm Nat)
      (fact : (PresenceNormalForm.Atom.tyLe lhs rhs).Holds CommonNominalFullCarrier.model m) :
      ContextDerives [] m context (.ordinary lhs) (.ordinary rhs) := by
    apply ((compiled_full_exact [] m context (.ordinary lhs) (.ordinary rhs)).mp ?_).2.2
    refine ⟨[.tyLe lhs rhs],compiled_ordinary context lhs rhs,?_⟩
    intro atom member
    cases List.mem_singleton.mp member
    exact fact
  exact ⟨fromConstraint _ _ arrived.1.1,fromConstraint _ _ arrived.1.2,
    fromConstraint _ _ arrived.2.1.1,fromConstraint _ _ arrived.2.1.2,
    fromConstraint _ _ arrived.2.2.1.1,fromConstraint _ _ arrived.2.2.1.2⟩

end Yulang.GeneralDeclarativeWitnessScopedNativeProjection358
