import Yulang.GeneralDeclarativeI65I74OpaqueVisibility448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Opaque448.Roster
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open RetainedSplit446.LocalHeader (selectedHeader selected_header_exact446)
open CommonRoleOutermostResolver (All₂)
open Checker408 (Problem)

structure BareRow (s : GeneralDeclarativeI65.State) (d : Declaration) where
  key : Nat
  bare : d.head = [.app key []]
  use : Use s.current.environment key 0
  mode : use.mode = .declared []
  table : s.modes[key]? = some []
  noWhere : d.requirements = []
  covered : DeclarationCovered s.current.environment d
  checked : DeclarationChecked (authoredRegistry s.current).constructors (authoredRegistry s.current).roles d

/-- A bare-name head can distinguish nominal identities only when the
actual inspected lower has independently checked physical authority.
A missing author or an undecided route is not a rigid mismatch. -/
structure BarePoint (s : GeneralDeclarativeI65.State) (q : Request) where
  arg : Capture
  asked : q.demand.arguments = [arg]
  rootOriginal : Origin
  authored : rootOriginal ∈ s.origins
  actualLower : rootOriginal.slot = arg.lower
  actualUpper : rootOriginal.slot = arg.upper
  key : Nat
  exact : rootOriginal.endpoint = .nominal key []
  physical : SinglePhysical s arg.lower

private theorem nameModeTransport {env : GeneralDeclarativeWitnessConstructorModes357.Environment}
    {k l : Nat} (eq : k = l) (use : Use env k 0) :
    names (show Use env l 0 from eq ▸ use).mode 0 = names use.mode 0 := by
  cases eq
  rfl

def BareRow.headRead {s q d} (b : BareRow s d) (o : BarePoint s q) (same : b.key = o.key) :
    SourceHead s q d := by
  refine .ordered (fun _ => emptyCapture403) ?_
  rw [b.bare,o.asked,same]
  let use : Use s.current.environment o.key 0 := same ▸ b.use
  have fromBody : names use.mode 0 = some [] := by
    change names (same ▸ b.use).mode 0 = some []
    have h : names b.use.mode 0 = some [] := by rw [b.mode]; rfl
    exact (nameModeTransport same b.use).trans h
  have table : s.modes[o.key]? = some [] := same ▸ b.table
  let cmp : DeclaredComparison s.current.environment s.current.ordinary s.modes false
    (.nominal o.key []) (.nominal o.key []) := by
      refine ⟨?_,.nominal table (.nil false),.nominal table (.nil false),.nominal table .nil⟩
      intro site actual
      have atKey : site = (o.key,0) := by
        simpa [GeneralDeclarativeWitnessSparseIntervals357.visited.eq_def,
          GeneralDeclarativeWitnessSparseIntervals357.visitedList.eq_def] using actual
      subst site
      exact ⟨use,[],fromBody,table⟩
  let window : ModeWindow s o.arg (.app o.key []) :=
    ⟨o.rootOriginal,o.rootOriginal,o.actualLower ▸ .direct,o.actualUpper ▸ .direct,
      o.authored,o.authored,o.key,[],rfl,[],[],o.exact,o.exact,
      by rw [o.exact]; exact cmp⟩
  refine .cons (.declared (found := []) window ?_) .nil
  change DeepRead s (fun _ => emptyCapture403) false (.app o.key [])
    o.rootOriginal.endpoint o.rootOriginal.endpoint []
  rw [o.exact]
  exact .nominal use fromBody table .nil

def BareRow.mismatch {s q d} (b : BareRow s d) (o : BarePoint s q) (diff : b.key ≠ o.key) :
    RigidCandidateMiss s q d :=
  ⟨0,o.arg,by rw [o.asked]; rfl,b.key,[],by rw [b.bare]; rfl,b.use,[],b.mode,
    ⟨o.rootOriginal,o.authored,o.actualLower ▸ .direct,o.physical,o.key,[],o.exact,
      b.key,[],rfl,diff⟩⟩

def BareRow.assess {s q d} (b : BareRow s d) (o : BarePoint s q) (here : d ∈ visible s q) :
    Assessment s q d :=
  if same : b.key = o.key then .matched ⟨here,b.covered,b.checked.signature,b.headRead o same⟩
  else .incompatible (b.mismatch o same)

inductive BareRows (s : GeneralDeclarativeI65.State) : List Declaration → Type where
  | nil : BareRows s []
  | next {d row} (first : BareRow s d) (tail : BareRows s row) : BareRows s (d :: row)

def BareRows.living {s : GeneralDeclarativeI65.State} {rows} (key : Nat) :
    BareRows s rows → List Declaration
  | .nil => []
  | .next (d := d) x xs => if x.key = key then d :: xs.living key else xs.living key

def BareRows.tape {s q rows} (o : BarePoint s q) (data : BareRows s rows)
    (all : ∀ d ∈ rows, d ∈ visible s q) : CandidateTape s q rows :=
  match data with
  | .nil => .nil
  | .next (d := d) x xs =>
    .next (x.assess o (all d List.mem_cons_self))
      (xs.tape o (fun r here => all r (List.mem_cons_of_mem _ here)))

theorem bare_roster_keeps_all_hits_and_no_waits448 {s q rows} (o : BarePoint s q)
    (data : BareRows s rows) (all : ∀ d ∈ rows, d ∈ visible s q) :
    (data.tape o all).live = data.living o.key ∧ (data.tape o all).waits = false := by
  induction data with
  | nil => exact ⟨rfl,rfl⟩
  | next r rest ih =>
    have tail := ih (fun d here => all d (List.mem_cons_of_mem _ here))
    by_cases same : r.key = o.key <;> simp [BareRows.tape,BareRows.living,BareRow.assess,same,
      CandidateTape.live,CandidateTape.waits,tail.1,tail.2]

theorem actual_whole_bare_single_match_selects448 {s q d} (o : BarePoint s q)
    (roster : BareRows s (visible s q)) (safe : ¬GeneralDeclarativePriority321.RootRecurs s.current.ordinary q.demand)
    (one : roster.living o.key = [d]) :
    TapedMatch s q (roster.tape o (fun _ inScope => inScope)) d := by
  have considered := bare_roster_keeps_all_hits_and_no_waits448 o roster (fun _ inScope => inScope)
  exact ⟨safe,considered.2,considered.1.trans one⟩

end Yulang.GeneralDeclarativeI65.I72.Opaque448.Roster
