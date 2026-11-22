import Yulang.GeneralDeclarativeNestedTail332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedSeek332
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeNestedTail332 (peel isTerminal follow withScripts ClosedAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Independently read a finite selected RHS index until a terminal is
visible. The budget is a bound on this syntax read, not a premise or
a claim about stabilization, rejection, or the language resolver. -/
def seek (src : Sources s) (root : Nat) : Nat → Option (List Nat)
  | 0 => do
    let rhs ← src.visible root
    let _ ← isTerminal (peel rhs).2
    pure []
  | fuel+1 => do
    let rhs ← src.visible root
    let stop := (peel rhs).2
    match stop with
    | .variable n => (seek src n fuel).map (List.cons n)
    | _ =>
      let _ ← isTerminal stop
      pure []

def seeking (src : Sources s) (budget : Nat) : Sources s :=
  withScripts src (fun n => seek src n budget)


theorem checked_result {s : State} (src : Sources s) (n budget : Nat)
    (got : (seeking src budget).spines n = some (fields,terminal)) :
    GeneralDeclarativeRecordSpine330.Spine s n fields terminal :=
  (seeking src budget).spine_sound n fields terminal got

theorem exact_path {s : State} (src : Sources s) (root : Nat) {found : ClosedAt s root}
    (scanned : seek src root fuel = some path)
    (checked : follow src root path = some found) :
    (seeking src fuel).spines root = some found.val := by
  simp [seeking,withScripts,scanned,checked]


theorem length_bound {s : State} (src : Sources s)
    (ran : seek src root fuel = some path) : path.length ≤ fuel := by
  induction fuel generalizing root path with
  | zero =>
    cases opened : src.visible root with
    | none => simp [seek,opened] at ran
    | some rhs =>
      cases last : isTerminal (peel rhs).2 with
      | none => simp [seek,opened,last] at ran
      | some stop =>
        have nil : path = [] := by simpa [seek,opened,last] using ran.symm
        simp [nil]
  | succ fuel ih =>
    cases opened : src.visible root with
    | none => simp [seek,opened] at ran
    | some rhs =>
      cases last : (peel rhs).2 with
      | «variable» next =>
        cases got : seek src next fuel with
        | none => simp [seek,opened,last,got] at ran
        | some rest =>
          have same : next::rest = path := by simpa [seek,opened,last,got] using ran
          subst path
          exact Nat.succ_le_succ (ih got)
      | primitive tag args =>
        cases tag <;> cases args <;> simp [seek,opened,last,isTerminal] at ran
        all_goals rw [last] at ran; cases Option.some.inj ran; exact Nat.zero_le _
      | record | nominal | variant | join =>
        all_goals simp [seek,opened,last,isTerminal] at ran


/-- Exact syntactic route in the selected index; not model equality
and not a source-availability oracle. -/
inductive Path (src : Sources s) : Nat → List Nat → Prop where
  | closed (seen : src.visible root = some rhs)
      (last : GeneralDeclarativeRecordSpine330.Terminal (peel rhs).2) : Path src root []
  | next (seen : src.visible root = some rhs) (next : (peel rhs).2 = .variable n)
      (suffix : Path src n rest) : Path src root (n::rest)

theorem terminal_seen {e : Expr} (ending : GeneralDeclarativeRecordSpine330.Terminal e) :
    ∃ cert, isTerminal e = some cert := by
  cases ending with
  | width => exact ⟨⟨.width⟩,rfl⟩
  | exactEnd => exact ⟨⟨.exactEnd⟩,rfl⟩

theorem seek_complete_for_path {s : State} {src : Sources s} (walk : Path src root path)
    (enough : path.length ≤ fuel) : seek src root fuel = some path := by
  induction walk generalizing fuel with
  | @closed root rhs seen last =>
    obtain ⟨cert,stops⟩ := terminal_seen last
    cases fuel with
    | zero => simp [seek,seen,stops]
    | succ fuel =>
      cases h : (peel rhs).2 with
      | «variable» n => rw [h] at last; cases last
      | primitive | nominal | record | variant | join =>
        all_goals simp [seek,seen,h,stops]
  | @next root rhs n rest seen continues _ ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have more := ih (Nat.le_of_succ_le_succ enough)
      simp [seek,seen,continues,more]

end Yulang.GeneralDeclarativeNestedSeek332
