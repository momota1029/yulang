import Yulang.GeneralDeclarativeTaggedFixture340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeTaggedFixtureSelection340
open GeneralDeclarativeTaggedFixture340
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeTaggedInputs340 (complete pull)
open GeneralDeclarativeTaggedElection340 (Ranked Election)
open GeneralDeclarativeTaggedSelected340 (Selected)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeObserverGrowth330 (preserve)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeGrowth327 (Extends trans facts)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeCurrentReceipt330 (literal)
open GeneralDeclarativeTraceNames321 (names)
open CommonRoleOutermostResolver (Classify Dictionary)

theorem build_grows : Extends named endState := by
  let range := (complete inputs (reflexive _)).2.1
  exact trans (facts _ _) (trans
    (GeneralDeclarativeStableAssemble329.assemble keep spans fallback range).preserve.grows (facts _ _))

theorem initial_grows : Extends initial endState := trans keep_old_model.grows build_grows

def current : Supported endState (fun _ => False) := preserve p initial_grows

def height (n : Nat) : Nat := if n < 3 then 1 else 0
def up (p : Nat × Nat) : Bool := decide (height p.1 ≤ height p.2)
def ok_atom (a : PresenceNormalForm.Atom Nat) : Bool :=
  match a with
  | .tyLe (.var l) (.var h) => up (l,h)
  | _ => true
def flatOK (r : Equation) : Bool :=
  match r.right with
  | .variable n => decide (height r.left = height n)
  | _ => true
def descends (r : Equation) : Bool :=
  match r.right with
  | .variable _ => true
  | other => (names other).all (fun n => decide (height n < height r.left))

theorem ranked : Ranked endState height := by
  have flow : endState.normal.intervals.all up = true := by decide +kernel
  have atoms : endState.normal.ordinary.all ok_atom = true := by decide +kernel
  have flat : endState.equations.all flatOK = true := by decide +kernel
  have deeper : endState.equations.all descends = true := by decide +kernel
  constructor
  · intro x y proof
    induction proof with
    | interval e => exact of_decide_eq_true (List.all_eq_true.mp flow _ e)
    | constraint e => exact of_decide_eq_true (List.all_eq_true.mp atoms _ e)
    | refl => exact Nat.le_refl _
    | trans _ _ left right => exact Nat.le_trans left right
  · intro x y known
    exact of_decide_eq_true (List.all_eq_true.mp flat _ known)
  · intro row inState n used notVar
    have ok := List.all_eq_true.mp deeper _ inState
    cases raw : row.right with
    | «variable» n => exact False.elim (notVar n raw)
    | primitive | nominal | record | variant | join =>
      unfold descends at ok
      rw [raw] at ok used
      exact of_decide_eq_true (List.all_eq_true.mp ok _ used)

def waiting (_ : Demand) (_ : Declaration) : Prop := False

theorem candidate : Election current registry interpretation waiting d chosen := by
  have seen := pull read initial_grows
  constructor
  · intro cap requested
    cases List.mem_singleton.mp requested
    exact .inr ⟨7,whole,seen.lower⟩
  · exact ⟨height,ranked⟩
  · rintro ⟨_,_,bad⟩
    exact bad
  · exact ⟨⟨List.mem_cons_self,rfl⟩,.cons
      (.merged ⟨7,whole,whole,GeneralDeclarativePlainFixture323.merged,[0,1],payloadCode,
        seen,GeneralDeclarativePlainFixture323.normalized,rfl,rfl⟩) .nil⟩
  · intro other accepted
    cases List.mem_singleton.mp accepted.1.1
    rfl

def selected : Selected current [] registry interpretation waiting d chosen [] where
  slice := ⟨initial,p,initial_grows,GeneralDeclarativeObserverGrowth330.sources_grow p initial_grows⟩
  keep := keep
  named := named
  spans := spans
  reads := []
  input := inputs
  fallback := fallback
  targets := targets
  ordinary := endState
  compiler := actual_compile
  receipt := literal (reflexive _)
  retained := fun _ h => h
  elected := candidate

theorem classification : Classify (Rule current [] registry interpretation waiting) d (.selected (.node 97 [])) :=
  ⟨.selected 97 [],.selected (.whole selected) .nil,.selected .nil (.selected rfl)⟩

end Yulang.GeneralDeclarativeTaggedFixtureSelection340
