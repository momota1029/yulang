import Yulang.GeneralDeclarativeRecordFieldRead330
import Yulang.GeneralDeclarativeStableAssemble329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordPoints330
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeRecordSpine330 (Spine exact_subtraction tail_append)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeNewNames321 (numbered supply after old_plus_extra)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEntailment320 (Entails model_append literal conservative_append appendFacts)
open GeneralDeclarativeGrowth327 (Extends facts trans fits)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm record_congr)
open GeneralDeclarationPatterns (normalize)
open CommonRoleCanonicalRows (Row)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCommonBridge (Assignment)

/-- Point-capture fields: the selected labels and their source order
are kept, while the expressions can be arbitrary supported inline payloads.
Simultaneous allocation is after all old names, targets and RHS names. -/
def expanded : Expr → List Expr
  | .variable _ => []
  | e => [e]
def fieldName (e : Expr) (fresh : Nat) : Nat :=
  match e with
  | .variable old => old
  | _ => fresh
def stepName (e : Expr) (fresh : Nat) : Nat := fresh + (expanded e).length
def expressions (picked : Row Expr) (tail : Expr) : List Expr :=
  picked.flatMap (fun f => expanded f.2) ++ [tail]
def seed (s : State) (root : Nat) (protect : List Nat) (picked : Row Expr) (tail : Expr) : Nat :=
  after ((stateNames s ++ root :: protect) ++ (expressions picked tail).flatMap names)
def readFrom : Row Expr → Nat → Expr
  | [], n => .variable n
  | (key,e)::xs,n => .record key (.variable (fieldName e n)) (readFrom xs (stepName e n))

inductive Layout : Row Expr → Row Expr → List Nat → Prop where
  | nil : Layout [] [] []
  | cons : Layout sources codes binders →
      Layout ((key,e)::sources) ((key,.variable v)::codes) (v::binders)

def usesFrom : Row Expr → List Nat → Nat → Nat → List (Nat × Capture)
  | (_,e)::src, v::vs, tailBinder, n =>
    (v,point (fieldName e n)) :: usesFrom src vs tailBinder (stepName e n)
  | _, _, tailBinder, n => [(tailBinder,point n)]

theorem walk (layout : Layout src cooked binders) (tailBinder first : Nat) :
    Walk .actual (readFrom src first) (withTail cooked (.variable tailBinder))
      (occurrences (usesFrom src binders tailBinder first)) := by
  induction layout generalizing first with
  | nil => exact .capture
  | cons _ ih => exact .record .capture (ih _)

theorem spans (s : State) (src : Row Expr) (binders : List Nat) (tailBinder first : Nat) :
    ∀ use ∈ usesFrom src binders tailBinder first, Bounds s use.2 := by
  induction src generalizing binders first with
  | nil =>
    intro use found
    cases List.mem_singleton.mp found
    exact point_bounded s _
  | cons here rest ih =>
    cases binders with
    | nil =>
      intro use found
      cases List.mem_singleton.mp found
      exact point_bounded s _
    | cons v vs =>
      intro use found
      rcases List.mem_cons.mp found with rfl|other
      · exact point_bounded s _
      · exact ih vs _ use other

theorem precise (src : Row Expr) (rhs : Expr) (first : Nat) (m : Assignment)
    (given : ∀ e ∈ numbered first (expressions src rhs), GeneralDeclarativeEntailment320.Holds m e) :
    Equivalent
      (value (GeneralDeclarativeHead320.environment m) .actual (readFrom src first))
      (value (GeneralDeclarativeHead320.environment m) .actual (withTail src rhs)) := by
  induction src generalizing first with
  | nil => exact given _ List.mem_cons_self
  | cons here rest ih =>
    rcases here with ⟨key,e⟩
    cases e
    case «variable» v =>
      exact record_congr key (eqv_refl _) (ih first given)
    all_goals
      exact record_congr key (given _ List.mem_cons_self)
        (ih (first+1) (fun e used => given e (List.mem_cons_of_mem _ used)))

def named (s : State) (root : Nat) (keep : List Nat) (picked : Row Expr) (rhs : Expr) : State :=
  appendFacts s (supply s (root::keep) (expressions picked rhs))
def readRow (s : State) (root : Nat) (keep : List Nat) (picked : Row Expr) (rhs : Expr) : Equation :=
  ⟨root,readFrom picked (seed s root keep picked rhs)⟩
def ready (s : State) (root : Nat) (keep : List Nat) (picked : Row Expr) (rhs : Expr) : State :=
  appendFacts (named s root keep picked rhs) [readRow s root keep picked rhs]

theorem observed {s : State} {p : Supported s done}
    (source : Spine (restriction p) arg.center raw terminal) (bounds : Bounds s arg)
    (keys : fields.Nodup) (copied : order (CommonRoleCanonicalRows.normalize raw) fields = some picked)
    (layout : Layout picked pattern binders)
    (compiled : translate c i (normalize pat) = some (withTail pattern (.variable tailBinder)))
    (keep : List Nat) :
    let rhs := tailExpr raw fields terminal
    let n := seed s arg.center keep picked rhs
    let t := ready s arg.center keep picked rhs
    Retains s t keep ∧ One t c i arg pat (usesFrom picked binders tailBinder n) := by
  let root := arg.center
  let rhs := tailExpr raw fields terminal
  let seedName := seed s root keep picked rhs
  let middle := named s root keep picked rhs
  let row := readRow s root keep picked rhs
  let t := ready s root keep picked rhs
  have grown : Extends s t := trans (facts _ _) (facts _ _)
  have entailed : Entails middle row := by
    intro m valid
    have sat := (model_append _).mp valid
    have orig := exact_subtraction source keys copied m sat.1
    have read := precise picked rhs seedName m sat.2
    exact eqv_trans orig (eqv_symm read)
  refine ⟨⟨grown,?_⟩,⟨fits grown bounds,_,_,compiled,.row (List.mem_append_right _ List.mem_cons_self),
    walk layout tailBinder seedName⟩⟩
  intro m valid
  obtain ⟨witness,kept⟩ := old_plus_extra s (root::keep) (expressions picked rhs) m valid
  refine ⟨_,(conservative_append (s := middle) (rows := [row]) (fun e known => ?_) _).mpr witness,?_⟩
  · cases List.mem_singleton.mp known
    exact entailed
  · intro v old
    rcases List.mem_append.mp old with a|b
    · exact kept v (List.mem_append_left _ a)
    · exact kept v (List.mem_append_right _ (List.mem_cons_of_mem _ b))


/-- The older name-only endpoint trace cannot look under a literal
inline record field. This is a limit of this positive proof relation,
not a rejection or blockedness theorem for the language. -/
theorem endpoint_spelling {s : State}
    (seen : GeneralDeclarativeTrace321.Trace s mode root (.record key capture tail) uses) :
    ∃ owner field rest,
      (⟨owner,.record key (.variable field) (.variable rest)⟩ : Equation) ∈ s.equations := by
  cases seen
  case record linked slot _ _ => exact ⟨_,_,_,slot⟩

end Yulang.GeneralDeclarativeRecordPoints330
