import Yulang.GeneralDeclarativeI65State365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (Legal visited names)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWhere319 (Capture)

theorem two_uses_of_one_written_constructor_agree {e} {name k l}
    (a : Use e name k) (b : Use e name l) : k = l := by
  have row := Option.some.inj (a.actual.symm.trans b.actual)
  exact a.exactArity.symm.trans ((congrArg (fun written => written.parameters.length) row).trans b.exactArity)

/-- An occurrence's authorized nominal observations share the exact
written constructor and kind-vector arity at both authored positions.
This does not alone prove that arbitrary payload subpatterns match. -/
theorem same_written_arity_at_both_origins {s : State} {arg : Capture} {pat : Pattern}
    (w : ModeWindow s arg pat)
    (source : Use s.current.environment w.name w.arguments.length) :
    w.arguments.length = w.firstArgs.length ∧ w.arguments.length = w.lastArgs.length := by
  have one : Legal s.current.environment s.modes (w.name,w.firstArgs.length) := by
    apply w.modeRead.actualSource
    rw [w.firstHead]
    exact List.mem_append_left _ (by rw [visited]; exact List.mem_cons_self)
  have two : Legal s.current.environment s.modes (w.name,w.lastArgs.length) := by
    apply w.modeRead.actualSource
    rw [w.lastHead]
    exact List.mem_append_right _ (by rw [visited]; exact List.mem_cons_self)
  obtain ⟨low,_,_,_⟩ := one
  obtain ⟨high,_,_,_⟩ := two
  exact ⟨two_uses_of_one_written_constructor_agree source low,two_uses_of_one_written_constructor_agree source high⟩

/-- The mode vector at a visited physical constructor position is
equal at both ends under the authoritative sparse registry, not
merely equal after inherited invariance changes effective direction. -/
theorem same_mode_vector_at_both_origins {s : State} {arg : Capture} {pat : Pattern}
    (w : ModeWindow s arg pat) :
    ∃ low : Use s.current.environment w.name w.firstArgs.length,
    ∃ high : Use s.current.environment w.name w.lastArgs.length,
    ∃ parameters,
      names low.mode w.firstArgs.length = some parameters ∧
      names high.mode w.lastArgs.length = some parameters ∧
      s.modes[w.name]? = some parameters := by
  have one : Legal s.current.environment s.modes (w.name,w.firstArgs.length) := by
    apply w.modeRead.actualSource
    rw [w.firstHead]
    exact List.mem_append_left _ (by rw [visited]; exact List.mem_cons_self)
  have two : Legal s.current.environment s.modes (w.name,w.lastArgs.length) := by
    apply w.modeRead.actualSource
    rw [w.lastHead]
    exact List.mem_append_right _ (by rw [visited]; exact List.mem_cons_self)
  obtain ⟨lo,declared,actual,there⟩ := one
  obtain ⟨hi,prior,seen,h⟩ := two
  have all := Option.some.inj (h.symm.trans there)
  exact ⟨lo,hi,declared,actual,all ▸ seen,there⟩

end Yulang.GeneralDeclarativeI65
