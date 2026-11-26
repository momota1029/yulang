import Yulang.GeneralDeclarativeI65I74MixedFixedSource442
import Yulang.GeneralDeclarativeI65I74RefPositionEntry441

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)
open Checker408 (Problem)
open RefPositions441 (pattern)
open CommonRoleOutermostResolver (Dictionary)

def inputOnly (p : Problem) : Problem :=
  {p with root := {p.root with demand := {p.root.demand with outputs := []}}}

theorem inputOnly_visible (p : Problem) :
    visible (inputOnly p).state.core (inputOnly p).root = visible p.state.core p.root := rfl

theorem inputOnly_original_K2 (p : Problem) :
    RootCycle (inputOnly p).state (inputOnly p).root ↔ RootCycle p.state p.root := Iff.rfl

/-- The input comparison and capture do not inspect the will-be output.
This is a proof about the same authored input and occurrence, not a
claim that output erasure preserves selection or dictionary results. -/
def restoreOriginalHead {p : Problem} {d : Declaration}
    (a : RefPositions441.Original (inputOnly p).state (inputOnly p).root d) :
    SourceHead p.state.core p.root d := by
  cases h : a.head with
  | ordered capture reads => exact .ordered capture reads
  | joined joined =>
    rcases joined with ⟨tag,name,firstBinder,lastBinder,different,written,head,normal,use,co,
      sourceFirst,sourceLast,actual,firstValue,lastValue,actualValue,demanded,first,last,center,whole⟩
    exact .joined ⟨tag,name,firstBinder,lastBinder,different,written,head,normal,use,co,
      sourceFirst,sourceLast,actual,firstValue,lastValue,actualValue,demanded,first,last,center,whole⟩

def originalCandidate {p : Problem} {d : Declaration}
    (a : RefPositions441.Original (inputOnly p).state (inputOnly p).root d) :
    AuthoredCandidate p.state.core p.root d :=
  ⟨by simp [← inputOnly_visible p,a.only],a.covered,a.checked.signature,restoreOriginalHead a⟩

def originalTape {p : Problem} {d : Declaration}
    (a : RefPositions441.Original (inputOnly p).state (inputOnly p).root d) :
    CandidateTape p.state.core p.root (visible p.state.core p.root) :=
  ((inputOnly_visible p).symm.trans a.only).symm ▸ .next (.matched (originalCandidate a)) .nil

theorem originalTapedChoice {p : Problem} {d : Declaration}
    (a : RefPositions441.Original (inputOnly p).state (inputOnly p).root d) :
    TapedMatch p.state.core p.root (originalTape a) d := by
  have characteristics : ∀ rows (same : rows = [d]),
      let t : CandidateTape p.state.core p.root rows :=
        same.symm ▸ .next (.matched (originalCandidate a)) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows same
    cases same
    exact ⟨rfl,rfl⟩
  have h := characteristics _ ((inputOnly_visible p).symm.trans a.only)
  exact ⟨a.safe,h.1,h.2⟩

/-- Output source read only. It does not check that an assignment
constraint was retained, or turn missing retention into rejection. -/
def readNamedOutput442 (s : I72.State) {q : Request}
    (frame : AuthoredBodyFrame393 s.core q)
    (checked : DeclarationChecked (authoredRegistry s.core.current).constructors
      (authoredRegistry s.core.current).roles frame.decl)
    (i : Fin q.demand.outputs.length) : Option (NamedMixedOutput401 s.b6 frame i) := do
  match actual : lookup (authoredRegistry s.core.current).roles frame.decl
      q.demand.outputs[i].name with
  | none => none
  | some body =>
    match typed : s.b6.read q frame.ordinal i body with
    | none => none
    | some plan =>
      match formed : substituteMixedRhs401 (instantiateName401 (frame.slots body)) plan with
      | none => none
      | some rhs =>
        some ⟨body,(lookup_exact _ _ checked.identified.2.2.1 _ _).mp actual,plan,typed,rhs,formed⟩

theorem read_named_output_keeps_original_address_and_body442 {s : I72.State} {q : Request}
    {frame : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    {checked : DeclarationChecked (authoredRegistry s.core.current).constructors
      (authoredRegistry s.core.current).roles frame.decl} {a : NamedMixedOutput401 s.b6 frame i}
    (_h : readNamedOutput442 s (q := q) frame checked i = some a) :
    a.receipt.occurrence = q.occurrence ∧ a.receipt.outputOrdinal = i.val ∧
    a.receipt.original = q.demand.outputs[i] ∧
    s.b6.read q frame.ordinal i a.body = some a.plan ∧
    Supplies (authoredRegistry s.core.current).roles frame.decl q.demand.outputs[i].name a.body :=
  ⟨rfl,rfl,rfl,a.originalTyped,a.supplied⟩

theorem restored_input_is_exact442 {p : Problem} {d : Declaration}
    (a : RefPositions441.Original (inputOnly p).state (inputOnly p).root d) :
    preoutputInputOfHead399 (restoreOriginalHead a) (fun _ => emptyCapture403) = a.capture := rfl

/-- Original elected input along with a replayed *source receipt*, before
any fixed output equality. No verdict is added to the public checker. -/
structure Replay (p : Problem) where
  decl : Declaration
  original : RefPositions441.Original (inputOnly p).state (inputOnly p).root decl
  event : Event p.state p.root
  exactDecl : event.frame.decl = decl
  exactOrdinal : unfilterOrdinal395 (fun row : Declaration => row.role == p.root.demand.role)
    (authoredRegistry p.state.core.current).declarations 0 = some event.frame.ordinal
  exactInput : event.frame.input = original.capture
  noWhere : event.kids = []
  onlyOutput : p.root.demand.outputs.length = 1

def replay442 (p : Problem) (wire : RefPositions441.Wire) : Option (Replay p) := do
  match scope : visible p.state.core p.root with
  | [d] =>
    let a ← RefPositions441.replay441 (inputOnly p) d (inputOnly_visible p ▸ scope) wire
    let c := originalCandidate a
    let reg := authoredRegistry p.state.core.current
    match h : unfilterOrdinal395 (fun row : Declaration => row.role == p.root.demand.role)
        reg.declarations 0 with
    | none => none
    | some ordinal =>
      if authored : reg.declarations[ordinal]? = some d then
        if only : p.root.demand.outputs.length = 1 then
          let f := frameAtSource395 c.inScope ordinal authored unusedPlacement403
            (preoutputInputOfHead399 c.head (fun _ => emptyCapture403))
          let i : Fin p.root.demand.outputs.length := ⟨0,by rw [only]; decide⟩
          let output ← readNamedOutput442 p.state f a.checked i
          let e : Event p.state p.root := ⟨f,c.head,fun j =>
            (show i = j from Fin.ext (by
              have dj : j.val < 1 := Nat.lt_of_lt_of_eq j.isLt only
              change 0 = j.val
              omega)) ▸ output⟩
          some ⟨d,a,e,rfl,h,restored_input_is_exact442 a,
            by simp [e,Event.kids,frameWhereKids400,f,frameAtSource395,AuthoredBodyFrame393.clauses,
              a.noWhere,children],only⟩
        else none
      else none
  | _ => none

theorem replay_uses_exact_selected_original_input442 {p w r}
    (_h : replay442 p w = some r) :
    TapedMatch p.state.core p.root (originalTape r.original) r.decl ∧
    r.event.frame.input r.original.rowBinder =
      GeneralDeclarativeWitnessDeclaredState357.point r.original.rowName ∧
    r.event.frame.input r.original.valueBinder =
      GeneralDeclarativeWitnessDeclaredState357.point r.original.valueName ∧
    r.event.kids = [] :=
  ⟨originalTapedChoice r.original,r.exactInput ▸ r.original.rowCapture,
    r.exactInput ▸ r.original.valueCapture,r.noWhere⟩

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442
