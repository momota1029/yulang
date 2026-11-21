import Yulang.GeneralDeclarativeRepeatedActual323
import Yulang.GeneralDeclarativeCompileLists321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRigidSource323
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (HeadMeaning Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeRepeatedActual323 (Rigid eqAt BindsAt rigid_exact split_binds)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeBatch320 (zipFacts)
open GeneralDeclarativeEntailment320 (Holds Entails)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open CommonRoleOutermostResolver (All₂)

structure Scanned (s : State) (c : Constructors) (interp : Interpretation)
    (arg : Capture) (p : Pattern) (seen : List Occurrence) : Prop where
  exact : ∃ term raw code,
    Entails s ⟨arg.center,term⟩ ∧ translate c interp p = some raw ∧
    translate c interp (normalize p) = some code ∧ Rigid .actual term code seen
  bounds : Bounds s arg

theorem head_fact_exact {s : State} (view : Scanned s c interp arg p seen) (m : Assignment)
    (model : Models s m) (raw : translate c interp p = some expr) :
    Holds m ⟨arg.center,logical cap .actual expr⟩ ↔ BindsAt m cap seen := by
  obtain ⟨term,code1,code2,shown,translated,normalized,walk⟩ := view.exact
  have same : expr = code1 := Option.some.inj (raw.symm.trans translated)
  subst expr
  have actual := shown m model
  have a := compiled_normalized (variables := variables cap m) translated
  have b := translate_value (normalize p) (variables := variables cap m) normalized
  have sameValue : eqAt m (logical cap .actual code1) (logical cap .actual code2) := by
    simpa only [eqAt,logical_value] using (b ▸ a)
  have visited := rigid_exact m cap walk
  constructor
  · intro holds
    exact visited.mp (eqv_trans (eqv_symm actual) (eqv_trans holds sameValue))
  · intro linked
    exact eqv_trans actual (eqv_trans (visited.mpr linked) (eqv_symm sameValue))

/-- Head and fixed-capture checks are exact on all models, for a supplied
real scan. Compiler equation soundness no longer needs a separate
completeness claim for the syntactic Derives proof system. -/
theorem head_result {s : State} (view : Scanned s c interp arg p seen)
    (bound : ∀ m, Models s m → BindsAt m cap seen) :
    Result s (headFact c interp cap arg p) := by
  obtain ⟨_,raw,_,_,written,_,_⟩ := view.exact
  refine ⟨[⟨arg.center,logical cap .actual raw⟩],by simp [headFact,written],?_⟩
  intro eq listed m model
  cases List.mem_singleton.mp listed
  exact (head_fact_exact view m model written).mpr (bound m model)

inductive Ordered (s : State) (c : Constructors) (interp : Interpretation) :
    List Capture → List Pattern → List Occurrence → Prop where
  | nil : Ordered s c interp [] [] []
  | cons : Scanned s c interp arg p one → Ordered s c interp args ps rest →
      Ordered s c interp (arg::args) (p::ps) (one++rest)

theorem ordered_results {s : State} (reads : Ordered s c interp args ps seen)
    (bound : ∀ m, Models s m → BindsAt m cap seen) :
    All₂ (fun arg p => Result s (headFact c interp cap arg p)) args ps := by
  induction reads with
  | nil => exact .nil
  | cons one rest ih =>
    exact .cons (head_result one (fun m valid => (split_binds .. |>.mp (bound m valid)).1))
      (ih (fun m valid => (split_binds .. |>.mp (bound m valid)).2))

theorem compiled_results {s : State} (reads : Ordered s c interp args ps seen)
    (bound : ∀ m, Models s m → BindsAt m cap seen) :
    Result s (zipFacts (headFact c interp cap) args ps) :=
  zip_result (ordered_results reads bound)

end Yulang.GeneralDeclarativeRigidSource323
