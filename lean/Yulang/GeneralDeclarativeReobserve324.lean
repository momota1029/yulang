import Yulang.GeneralDeclarativeSharedNF324
import Yulang.GeneralDeclarativeHeadDetermines320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeReobserve324
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Models Equation variables_eq byMode)
open GeneralDeclarativeEntailment320 (Holds Entails)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeOutputs320 (OutputMeaning bodyCapture bodyPattern)
open GeneralDeclarativeAssocModel323 (actual_output)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open GeneralDeclarativeHeadDetermines320 (pattern_congruent)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralDeclarationPatterns (normalize)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCommonBridge (Assignment)

def Reobserves (s : State) (impl : GeneralDeclarations.Declaration) (left right : Nat → Capture) : Prop :=
  ∀ m, Models s m →
    (∀ n ∈ impl.inputNames, Equivalent (m (left n).center).1 (m (right n).center).1) ∧
    (∀ n ∈ impl.outputNames, Equivalent (m (left n).center).1 (m (right n).center).1)

theorem rhs_value {s : State} {r : GeneralDeclarations.Registry} {out : GeneralSourceState.Output}
    (checked : Checked r) (visible : impl ∈ r.declarations)
    (supplied : Supplies r.roles impl out.name body)
    (agree : Reobserves s impl left right)
    (m : Assignment) (valid : Models s m) :
    Equivalent
      (GeneralDeclarativeDemand320.sourceValue r.constructors interp (bodyCapture d left body) m (bodyPattern body))
      (GeneralDeclarativeDemand320.sourceValue r.constructors interp (bodyCapture d right body) m (bodyPattern body)) := by
  cases supplied with
  | default rhs _ _ => exact eqv_refl _
  | explicit eq present _ =>
    apply pattern_congruent
    intro n mentioned
    have sc := (checked.2 impl visible).scope.2.1 eq present n mentioned
    rw [variables_eq,variables_eq]
    exact sc.elim ((agree m valid).1 n) ((agree m valid).2 n)

theorem ordinary_reobserved {s : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (agree : Reobserves s impl left right)
    (closed : StableUnder s (SourceEquation r interp d impl left)) :
    StableUnder s (SourceEquation r interp d impl right) := by
  apply stable_exact.mpr
  rintro row ⟨out,uses,body,covered,nf,compiled,rfl⟩ m valid
  have previous : SourceEquation r interp d impl left
      ⟨out.target,logical (bodyCapture d left body) .actual nf⟩ :=
    ⟨out,uses,body,covered,nf,compiled,rfl⟩
  have witness := (actual_output checked visible covered compiled m).mp
    (stable_exact.mp closed _ previous m valid)
  obtain ⟨old,proven,source⟩ := witness
  have equal := GeneralDictionaryAssociatedProvenance.supplies_unique r.roles impl
    (checked.2 impl visible).identified.2.2.1 out.name old body proven covered
  cases equal
  exact (actual_output checked visible covered compiled m).mpr
    ⟨body,covered,eqv_trans source (rhs_value (interp := interp) (d := d) checked visible covered agree m valid)⟩

end Yulang.GeneralDeclarativeReobserve324
