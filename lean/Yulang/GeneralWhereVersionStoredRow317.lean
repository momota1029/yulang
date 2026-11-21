import Yulang.GeneralWhereVersionReuseCertificate317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 52000000
namespace Yulang.GeneralWhereVersionStoredRow317
open GeneralDeclarations (Registry Clause)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatExpressions (translate value)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedEndpointAddress315 (Side atCell fields coherent)
open GeneralVersionedEndpointSourceKey315 (SourceRow)

/-- A validated journal certificate names the source-level cell and its
actual versioned target. Raw slot presence alone is not this certificate. -/
structure Endpoint (p : Plan roles) (side : Side) (clause : Clause)
    (i : Nat) (row : Equation) : Prop where
  origin : SourceRow p side clause i row
  target : row.target = atCell p side clause.id i row.expression

/-- If both positions are certified in the same checked source
configuration, equal versioned targets imply same-model equivalence of
the V8 obligations. No claim is made here that every existing raw slot
came from this journal or that the required configurations are reachable. -/
theorem same_target_iff {p q : Plan roles} {a b : Side} {c d : Clause} {i j : Nat}
    {one two : Equation}
    (checked : GeneralDeclarations.Checked p.packet.registry)
    (reg : p.packet.registry = q.packet.registry)
    (view : p.packet.context.interpretation = q.packet.context.interpretation)
    (seed : p.packet.context.state.seed = q.packet.context.state.seed)
    (vis : p.packet.declaration ∈ p.packet.registry.declarations)
    (old : q.packet.declaration ∈ q.packet.registry.declarations)
    (first : Endpoint p a c i one) (last : Endpoint q b d j two)
    (same : one.target = two.target) (m : Assignment) :
    one.Holds (variables p m) m ↔ two.Holds (variables q m) m := by
  have address : atCell p a c.id i one.expression = atCell q b d.id j two.expression :=
    first.target.symm.trans (same.trans last.target)
  obtain ⟨_,decl,side,clause,pos,_⟩ := fields seed address
  subst b; subst j
  have equalDecl := GeneralDictionaryEmissionPlans.declaration_key_unique _ checked _ _
    vis (reg.symm ▸ old) decl
  have equalClause := GeneralVersionedCompoundRows313.key_unique Clause.id _
    p.packet.checked.identified.1 c d first.origin.listed (equalDecl.symm ▸ last.origin.listed) clause
  subst d
  obtain ⟨pat,found,compiled⟩ := first.origin.source
  obtain ⟨oldPat,oldFound,oldCompiled⟩ := last.origin.source
  have exactPattern := Option.some.inj (oldFound.symm.trans found)
  subst oldPat
  rw [← reg,← view] at oldCompiled
  have expression : one.expression = two.expression := Option.some.inj (compiled.symm.trans oldCompiled)
  have rhs : value (variables p m) a.mode one.expression = value (variables q m) a.mode two.expression := by
    rw [← expression] at address ⊢
    exact coherent seed address m
  unfold Equation.Holds
  rw [same,first.origin.mode,last.origin.mode,rhs]

end Yulang.GeneralWhereVersionStoredRow317
