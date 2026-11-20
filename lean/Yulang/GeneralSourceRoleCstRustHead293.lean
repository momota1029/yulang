import Yulang.GeneralSourceRoleCstExternalContract293

/-! Current Rust's TypeApplyArgument holds a TypeExpression node, not the
bare identifier token directly. This form is replayed from a Rust golden. -/
namespace Yulang.GeneralSourceRoleCstRustHead293
open GeneralSourceRoleCstTree293 (Tree)
open GeneralSourceRoleCstShapes293 (visible argumentName HasArgument argument_exact)
open GeneralSourceRoleExport292 (Aligned collect collect_exact)

def unwrap (t : Tree) : Option Tree :=
  match t with
  | .node .argument cs =>
    match visible cs with
    | [.node .head inner] => some (.node .argument inner)
    | _ => none
  | _ => none

def readArgument (t : Tree) : Option String := (unwrap t).bind argumentName

def ActualArgument (t : Tree) (name : String) : Prop :=
  ∃ cs inner, t = .node .argument cs ∧ visible cs = [.node .head inner] ∧
    visible inner = [.token .sigilIdentifier name]

theorem argument_exact_rust (t : Tree) (n : String) :
    readArgument t = some n ↔ ActualArgument t n := by
  constructor
  · intro h
    cases t with
    | token => cases h
    | node k cs =>
      cases k <;> try cases h
      cases shape : visible cs with
      | nil => simp [readArgument,unwrap,shape] at h
      | cons x xs =>
        cases xs with
        | cons y ys =>
          cases x <;> simp [readArgument,unwrap,shape] at h
        | nil =>
          cases x with
          | token => simp [readArgument,unwrap,shape] at h
          | node k inner =>
            cases k <;> simp [readArgument,unwrap,shape] at h
            obtain ⟨cs',e,binders⟩ := (argument_exact ..).mp h
            have same := (Tree.node.inj e).2
            subst cs'
            exact ⟨cs,inner,rfl,shape,binders⟩
  · rintro ⟨cs,inr,rfl,wrapper,leaf⟩
    simp [readArgument,unwrap,wrapper,(argument_exact ..).mpr ⟨inr,rfl,leaf⟩]

def readHead : Tree → Option (String × List String)
  | .node .head cs =>
    match visible cs with
    | .token .identifier n :: args => (collect readArgument args).map (n, ·)
    | _ => none
  | _ => none

def ActualHead (t : Tree) (name : String) (params : List String) : Prop :=
  ∃ cs args, t = .node .head cs ∧ visible cs = .token .identifier name :: args ∧
    Aligned ActualArgument args params

theorem head_exact_rust (t : Tree) (name : String) (params : List String) :
    readHead t = some (name,params) ↔ ActualHead t name params := by
  constructor
  · intro resolved
    cases t with
    | token => cases resolved
    | node k cs =>
      cases k <;> try cases resolved
      cases h : visible cs with
      | nil => simp [readHead,h] at resolved
      | cons first args =>
        cases first with
        | node => simp [readHead,h] at resolved
        | token k s =>
          cases k <;> simp [readHead,h] at resolved
          cases e : collect readArgument args with
          | none => simp [e] at resolved
          | some found =>
            have Is : s = name ∧ found = params := by simpa [e,and_comm] using resolved
            exact ⟨cs,args,rfl,Is.1 ▸ h,Is.2 ▸
              (collect_exact _ _ argument_exact_rust _ _).mp e⟩
  · rintro ⟨cs,args,rfl,shape,selected⟩
    simp [readHead,shape,(collect_exact _ _ argument_exact_rust _ _).mpr selected]

theorem direct_shallow_token_not_actual_argument (n : String) :
    readArgument (.node .argument [.token .sigilIdentifier n]) = none := rfl

end Yulang.GeneralSourceRoleCstRustHead293
