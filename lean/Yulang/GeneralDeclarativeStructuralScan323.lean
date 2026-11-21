import Yulang.GeneralDeclarativeRecordWalk323
import Yulang.GeneralDeclarativePlainCapture323
import Yulang.GeneralDeclarativeRigidBatch323
import Yulang.GeneralDeclarativeTraceCapture323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStructuralScan323
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeEntailment320 (Holds Entails)
open GeneralDeclarativeExactWalk323 (Exact)
open GeneralDeclarativeRepeatedActual323 (eqAt BindsAt)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeTermOccurrences322 (source_binders)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralDeclarativePlainCapture323 (WholeNames tag_head)

structure ReadBack (s : State) (c : Constructors) (interp : Interpretation)
    (arg : Capture) (p : Pattern) (observations : List Occurrence) : Prop where
  syntaxView : ∃ term raw code,
    Entails s ⟨arg.center,term⟩ ∧ translate c interp p = some raw ∧
    translate c interp (normalize p) = some code ∧ Exact .actual term code observations
  inRange : Bounds s arg

theorem actual_binders (atSource : ReadBack s c interp arg p observed) :
    observed.map Occurrence.binder = (normalize p).variables ∧
      ∀ o ∈ observed, o.mode = .actual := by
  obtain ⟨_,_,_,_,_,written,view⟩ := atSource.syntaxView
  exact ⟨(source_binders written view.walked).1,
    (GeneralDeclarativeTermOccurrences322.actual_positions view.walked).2⟩

theorem head_row_exact {s : State} (atSource : ReadBack s c interp arg p observed)
    (written : translate c interp p = some raw) (m : Assignment) (valid : Models s m) :
    Holds m ⟨arg.center,logical cap .actual raw⟩ ↔ BindsAt m cap observed := by
  obtain ⟨term,raw',code,ord,original,normalized,view⟩ := atSource.syntaxView
  cases Option.some.inj (written.symm.trans original)
  have ref := compiled_normalized (variables := variables cap m) written
  have norm := translate_value (normalize p) (variables := variables cap m) normalized
  rw [← norm] at ref
  have same : eqAt m (logical cap .actual raw) (logical cap .actual code) := by
    simpa only [eqAt,logical_value] using ref
  have here := ord m valid
  constructor
  · intro eq
    exact (view.semantic m cap).mp (eqv_trans (eqv_symm here) (eqv_trans eq same))
  · intro obs
    exact eqv_trans here (eqv_trans ((view.semantic m cap).mpr obs) (eqv_symm same))

/-- Two source-backed head forms. In a closed structural form the
occurrences are exact. In a grouped variant with a plain-variable list,
the source rule itself supplies the whole payload to each occurrence. -/
inductive Read (s : State) (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (arg : Capture) (p : Pattern) : Prop where
  | structural : ReadBack s c interp arg p observed →
      (∀ m, Models s m → BindsAt m capture observed) → Read s c interp capture arg p
  | merged : normalize p = .variant tag payload →
      GeneralCandidateInspection.plainNames payload = some names →
      translate c interp payload = some code → translate c interp p = some raw →
      Entails s ⟨arg.center,.variant tag term⟩ → WholeNames s capture term names →
      Read s c interp capture arg p

theorem recipe {s : State} (read : Read s c interp capture arg p) :
    Result s (headFact c interp capture arg p) := by
  cases read with
  | structural real binders =>
    obtain ⟨_,raw,_,_,translated,_,_⟩ := real.syntaxView
    refine ⟨[⟨arg.center,logical capture .actual raw⟩],by simp [headFact,translated],?_⟩
    intro row wanted m valid
    cases List.mem_singleton.mp wanted
    exact (head_row_exact real translated m valid).mpr (binders m valid)
  | merged normalized wanted spelling actual envelope captures =>
    exact tag_head normalized wanted spelling actual envelope captures

end Yulang.GeneralDeclarativeStructuralScan323
