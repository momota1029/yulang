import Yulang.CoreInference

/-! A checked source boundary for executable inference on Core. In particular
`Required.decode`'s default case must never turn new syntax into a literal. -/
namespace Yulang.Core.InferenceSyntax

abbrev Term := Required.Term

def supported : Term → Bool
  | .var _ | .lit _ | .emptyRecord => true
  | .lam body | .fst body | .snd body | .field _ body | .variant _ body => supported body
  | .app left right | .letE none left right | .pair left right |
      .record _ left right | .recordDefault _ left right => supported left && supported right
  | .branch condition yes no => supported condition && supported yes && supported no
  | _ => false

@[simp] theorem supported_embed (e : Inference.Expr) : supported (Required.embed e) = true := by
  induction e <;> simp_all [Required.embed, supported]

theorem embed_decode (e : Term) (valid : supported e = true) :
    Required.embed (Required.decode e) = e := by
  cases e <;> try simp_all only [supported, Bool.and_eq_true, Bool.false_eq_true]
  case var | lit | emptyRecord => rfl
  case lam body => exact congrArg Expr.lam (embed_decode body valid)
  case fst body => exact congrArg Expr.fst (embed_decode body valid)
  case snd body => exact congrArg Expr.snd (embed_decode body valid)
  case field label body => exact congrArg (Expr.field label) (embed_decode body valid)
  case variant label body => exact congrArg (Expr.variant label) (embed_decode body valid)
  case app left right =>
    simp only [Required.decode, Required.embed, embed_decode left valid.1, embed_decode right valid.2]
  case pair left right =>
    simp only [Required.decode, Required.embed, embed_decode left valid.1, embed_decode right valid.2]
  case record label left right =>
    simp only [Required.decode, Required.embed, embed_decode left valid.1, embed_decode right valid.2]
  case recordDefault label left right =>
    simp only [Required.decode, Required.embed, embed_decode left valid.1, embed_decode right valid.2]
  case branch condition yes no =>
    simp only [Required.decode, Required.embed, embed_decode condition valid.1.1,
      embed_decode yes valid.1.2, embed_decode no valid.2]
  case letE hint left right =>
    cases hint with
    | some => simp [supported] at valid
    | none =>
        have parts := Bool.and_eq_true_iff.mp valid
        simp only [Required.decode, Required.embed, embed_decode left parts.1, embed_decode right parts.2]

end Yulang.Core.InferenceSyntax
