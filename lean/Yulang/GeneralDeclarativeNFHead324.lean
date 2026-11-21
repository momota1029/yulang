import Yulang.GeneralDeclarativeStructuralScan323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNFHead324
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Bounds bounds_sound HeadMeaning)
open GeneralDeclarativeEntailment320 (Holds Entails)
open GeneralDeclarativeExactWalk323 (Exact)
open GeneralDeclarativeRepeatedActual323 (eqAt BindsAt)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize)

def fact (c : Constructors) (interp : Interpretation) (capture : Nat → Capture)
    (arg : Capture) (pattern : Pattern) : Option (List Equation) :=
  (translate c interp (normalize pattern)).map fun nf =>
    [⟨arg.center,logical capture .actual nf⟩]

theorem reads {s : State} (bounds : Bounds s arg)
    (proof : Result s (fact c interp capture arg pattern))
    (m : Assignment) (valid : Models s m) :
    HeadMeaning c interp capture m arg pattern := by
  obtain ⟨rows,compiled,closed⟩ := proof
  cases printed : translate c interp (normalize pattern) with
  | none => simp [fact,printed] at compiled
  | some nf =>
    have same : [⟨arg.center,logical capture .actual nf⟩] = rows := by simpa [fact,printed] using compiled
    subst rows
    have row := closed _ List.mem_cons_self m valid
    simp only [Holds,logical_value,translate_value (normalize pattern) printed] at row
    exact ⟨row,bounds_sound bounds m valid⟩

structure Scan (s : State) (c : Constructors) (interp : Interpretation)
    (arg : Capture) (pattern : Pattern) (uses : List Occurrence) : Prop where
  range : Bounds s arg
  observed : ∃ term nf, Entails s ⟨arg.center,term⟩ ∧
    translate c interp (normalize pattern) = some nf ∧ Exact .actual term nf uses

theorem exact_row {s : State} (view : Scan s c interp arg pattern uses)
    (printed : translate c interp (normalize pattern) = some nf) (m : Assignment) (valid : Models s m) :
    Holds m ⟨arg.center,logical cap .actual nf⟩ ↔ BindsAt m cap uses := by
  obtain ⟨term,nf',entails,compiled,exact⟩ := view.observed
  cases Option.some.inj (printed.symm.trans compiled)
  have real := entails m valid
  constructor
  · intro same
    exact (exact.semantic m cap).mp (eqv_trans (eqv_symm real) same)
  · intro shared
    exact eqv_trans real ((exact.semantic m cap).mpr shared)

theorem produces {s : State} (view : Scan s c interp arg pattern uses)
    (actual : ∀ m, Models s m → BindsAt m cap uses) :
    Result s (fact c interp cap arg pattern) := by
  obtain ⟨_,nf,_,written,_⟩ := view.observed
  refine ⟨[⟨arg.center,logical cap .actual nf⟩],by simp [fact,written],?_⟩
  intro row member m valid
  cases List.mem_singleton.mp member
  exact (exact_row view written m valid).mpr (actual m valid)

theorem old_agrees {arg : Capture} (old : translate c interp p = some raw)
    (fresh : translate c interp (normalize p) = some nf) (m : Assignment) :
    Holds m ⟨arg.center,logical capture .actual raw⟩ ↔
      Holds m ⟨arg.center,logical capture .actual nf⟩ := by
  have erasure := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
    (variables := variables capture m) old
  rw [← translate_value (normalize p) fresh] at erasure
  simp only [Holds,logical_value]
  exact ⟨fun h => eqv_trans h erasure,fun h => eqv_trans h (eqv_symm erasure)⟩

end Yulang.GeneralDeclarativeNFHead324
