import Yulang.CoreExpr

/-! NominalConstructions has a construction planner, not an expression AST.
Its model below checks the same site metadata and returns a plan; it does not
infer or execute the source expressions supplied at those sites. -/
namespace Yulang.Core.Construction
open NominalConstructions
abbrev Term := Core.Expr Signature.empty

def argument (a : Argument parameters) : Nat × LiteralCasts.Element × Term :=
  (a.parameter.val, a.original, .free a.original.site)

def embed (c : NominalConstructions.Construction parameters) : Term :=
  .construction c.constructor c.construction parameters (c.arguments.map argument)

theorem argument_injective : Function.Injective (argument (parameters := parameters)) := by
  intro a b same
  cases a with
  | mk pa oa =>
    cases b with
    | mk pb ob =>
      have p := congrArg Prod.fst same
      have o := congrArg (fun x => x.2.1) same
      simp only [argument] at p o
      have eq := Fin.ext p
      cases eq; cases o; rfl

private theorem arguments_injective :
    Function.Injective (List.map (argument (parameters := parameters))) := by
  intro a
  induction a with
  | nil => intro b same; cases b <;> simp_all
  | cons head tail ih =>
    intro b same
    cases b with
    | nil => simp at same
    | cons first rest =>
      simp only [List.map_cons, List.cons.injEq] at same
      have heads := argument_injective same.1
      have tails := ih same.2
      cases heads; cases tails; rfl

theorem embed_injective : Function.Injective (embed (parameters := parameters)) := by
  intro a b same
  cases a with
  | mk ac ai aa =>
    cases b with
    | mk bc bi ba =>
      simp only [embed, Core.Expr.construction.injEq] at same
      obtain ⟨rfl, rfl, args⟩ := same
      have eq := arguments_injective args.2
      cases eq; rfl

inductive Typing (fits : Casts.Compatibility) (registry : CastGraph.Registry n)
    (expected : Expectation parameters) : Term → Plan parameters → Prop where
  | build (c : NominalConstructions.Construction parameters) : registry.WellFormed →
      (∀ a ∈ c.arguments, SiteAllowed fits.Rel registry.Explicit expected a) →
      Typing fits registry expected (embed c) (c.plan expected)

def model (fits : Casts.Compatibility) (registry : CastGraph.Registry n)
    (expected : Expectation parameters) : TypingModel Signature.empty :=
  ⟨Unit, Plan parameters, fun _ => Typing fits registry expected⟩

theorem reflected (h : Typing fits registry expected expression plan) :
    ∀ c, embed c = expression → PlanTyping fits registry c expected plan := by
  cases h with
  | build other valid sites =>
    intro c eq
    have same := embed_injective eq
    cases same
    exact .build valid sites

theorem conservative (fits : Casts.Compatibility) (registry : CastGraph.Registry n)
    (expected : Expectation parameters) (c : NominalConstructions.Construction parameters)
    (plan : Plan parameters) :
    PlanTyping fits registry c expected plan ↔
      Core.Typing (model fits registry expected) () (embed c) plan := by
  constructor
  · intro h; cases h with | build valid sites => exact .build c valid sites
  · intro h
    exact reflected h c rfl

end Yulang.Core.Construction
