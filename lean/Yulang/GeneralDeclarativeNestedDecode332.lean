import Yulang.GeneralDeclarativeNestedSound332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedDecode332
open GeneralDeclarativeNestedSyntax332 (Node Nodes Fields Tail)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeNestedRun332 (run)
open GeneralDeclarativeNestedSound332 (sound)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)

def prepend (key : Nat) (head rest : Node) :
    Option { out : Node // out.code = Expr.record key head.code rest.code } :=
  match rest with
  | .capture b => some ⟨.record (.cons key head .nil) (.capture b),rfl⟩
  | .primitive .emptyRecord .nil => some ⟨.record (.cons key head .nil) .width,rfl⟩
  | .primitive .exactEmpty .nil => some ⟨.record (.cons key head .nil) .exactEnd,rfl⟩
  | .record fields tail => some ⟨.record (.cons key head fields) tail,rfl⟩
  | _ => none

abbrev Decoded (code : Expr) := { node : Node // node.code = code }
abbrev DecodedList (xs : List Expr) := { ns : Nodes // ns.codes = xs }

/- Reification follows the actual translated normalized expression.
This does not accept a second asserted pattern beside the compiler's
print. Unsupported tail syntax remains absent. -/
mutual
def decode (code : Expr) : Option (Decoded code) :=
  match code with
  | .variable x => some ⟨.capture x,rfl⟩
  | .primitive tag args =>
    (decodeMany args).map fun ⟨ns,exactly⟩ => ⟨.primitive tag ns,congrArg (Expr.primitive tag) exactly⟩
  | .nominal tag args =>
    (decodeMany args).map fun ⟨ns,exactly⟩ => ⟨.nominal tag ns,congrArg (Expr.nominal tag) exactly⟩
  | .record key front back => do
    let a ← decode front
    let b ← decode back
    let out ← prepend key a.val b.val
    pure ⟨out.val,by rw [out.property,a.property,b.property]⟩
  | .variant tag data =>
    (decode data).map fun ⟨a,exactly⟩ => ⟨.variant tag a,congrArg (Expr.variant tag) exactly⟩
  | .join front back => do
    let a ← decode front
    let b ← decode back
    pure ⟨.join a.val b.val,by rw [Node.code,a.property,b.property]⟩
termination_by structural code

def decodeMany (codes : List Expr) : Option (DecodedList codes) :=
  match codes with
  | [] => some ⟨.nil,rfl⟩
  | first::last => do
    let a ← decode first
    let b ← decodeMany last
    pure ⟨.cons a.val b.val,by rw [Nodes.codes,a.property,b.property]⟩
termination_by structural codes
end

def normalized (src : Sources s) (c : GeneralDeclarationPatterns.Constructors)
    (i : GeneralNominalInspection.Interpretation) (mode : GeneralNominalMaterialization.Mode)
    (input : Expr) (pat : GeneralDeclarationPatterns.Pattern) :
    Option (List GeneralDeclarativeTermWalk322.Occurrence) := do
  let code ← translate c i (normalize pat)
  let target ← decode code
  run src mode input target.val

theorem normalized_sound {src : Sources s}
    (performed : normalized src c i mode input pat = some uses) :
    ∃ code, translate c i (normalize pat) = some code ∧ Read s mode input code uses := by
  cases printed : translate c i (normalize pat) with
  | none => simp [normalized,printed] at performed
  | some code =>
    cases determined : decode code with
    | none => simp [normalized,printed,determined] at performed
    | some decoded =>
      have computed : run src mode input decoded.val = some uses := by
        simpa [normalized,printed,determined] using performed
      exact ⟨code,rfl,decoded.property ▸ sound src decoded.val computed⟩

end Yulang.GeneralDeclarativeNestedDecode332
