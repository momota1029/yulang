import Yulang.GeneralDeclarativeNestedIndex332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedTail332
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeRecordSpine330 (Spine Terminal)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleCanonicalRows (Row)

def peel : Expr → Row Expr × Expr
  | .record key data tail =>
    let (fields,stop) := peel tail
    ((key,data)::fields,stop)
  | other => ([],other)

theorem exact_peel (raw : Expr) : withTail (peel raw).1 (peel raw).2 = raw := by
  cases raw with
  | record key data tail =>
    have h := exact_peel tail
    simp only [peel,withTail]
    rw [h]
  | «variable» | primitive | nominal | variant | join => rfl
termination_by structural raw

def isTerminal (e : Expr) : Option (PLift (Terminal e)) :=
  match e with
  | .primitive .emptyRecord [] => some ⟨.width⟩
  | .primitive .exactEmpty [] => some ⟨.exactEnd⟩
  | _ => none

abbrev ClosedAt (s : State) (n : Nat) :=
  { out : Row Expr × Expr // Spine s n out.1 out.2 }

/-- Check an already identified finite source path against recorded
ordinary, supported RHSs. Missing evidence never manufactures a
terminal. This path check is not a recursive resolver/search. -/
def follow (src : Sources s) (root : Nat) (script : List Nat) : Option (ClosedAt s root) :=
  match read : src.visible root with
  | none => none
  | some rhs =>
    let part := peel rhs
    match script with
    | [] => do
      let stop ← isTerminal part.2
      pure ⟨part,by
        obtain ⟨owner,link,known⟩ := src.authorized root rhs read
        exact .inline link stop.down ((exact_peel rhs).symm ▸ known)⟩
    | next::later =>
      match nextHead : part.2 with
      | .variable found =>
        if h : found = next then do
          let suffix ← follow src next later
          pure ⟨(part.1++suffix.val.1,suffix.val.2),by
            obtain ⟨owner,link,known⟩ := src.authorized root rhs read
            have same : part.2 = .variable next := nextHead.trans (congrArg Expr.variable h)
            have shape : withTail part.1 (.variable next) = rhs :=
              same ▸ exact_peel rhs
            exact .prefixed link (shape.symm ▸ known) suffix.property⟩
        else none
      | _ => none
termination_by structural script

def withScripts {s : State} (original : Sources s) (script : Nat → Option (List Nat)) : Sources s :=
  ⟨original.visible,original.authorized,fun n => do
    let steps ← script n
    (follow original n steps).map Subtype.val,
    by
      intro n raw terminal printed
      cases hint : script n with
      | none => simp [hint] at printed
      | some path =>
        cases was : follow original n path with
        | none => simp [hint,was] at printed
        | some checked =>
          have eq : checked.val = (raw,terminal) := by simpa [hint,was] using printed
          exact (congrArg (fun arg => Spine s n arg.1 arg.2) eq) ▸ checked.property⟩

end Yulang.GeneralDeclarativeNestedTail332
