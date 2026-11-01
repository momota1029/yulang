import YulangClosure.Contracts
import YulangClosure.OriginalSourceGeneration

/-!
R196 source-only stopping surface; this is NOT a canonical inference model.

Parent: `YulangClosure.SourceProblem.InferenceSoundness` (Contracts.lean).
Selected SG authority: 2026-10-08-source-generalize-definition.md §2,
selecting the construction §§3–5. Its §3.1 literal rule retains the
independently fixed actual declaration and complete local typed relation.

Available original equations are not discarded: the selected native literal
Call rule for literal 0 fixes Value(Int), Result = Comp(empty,Int), and the
same literal/provider/current event in its authentic id Int frame. The
approved Original-ResultLiteral rule for literal 1 fixes original Data and
Result-port formation at its actual Application_N occurrence/telescope,
given its independent H_prim/H_return. Neither rule supplies the entire
original literal declaration and a full-language independent Simple-sub
constraint/readout interpretation. No absence of literal semantics or need
for a new semantic decision is inferred merely from a Lean parameter.

The theorem below locates precisely the first symbolic generator leaf for
ALL original Literal payloads and arbitrary source contexts/sites. It is
only an equation about the existing source rule program. In particular its
Formula.local is interpreted by OriginalSource.Local, including the original
Kernel.atom; it is not independent structural Store.Satisfied. Identifying
these two solution relations would hide the missing bridge.

First unresolved source application: construct the independently fixed
complete literal-declaration/readout equation at the same original scope,
assignment, value/root/event, including its value/effect constraints and all
original guards and alternatives. The source owner must then prove that an
independent solution supplies that atom. The inspected selected sources do
not provide this all-literal equation. This is an input/correspondence gap,
not a counterexample, a proof of semantic underdetermination, or a request to
choose a new literal rule. The full constructor inventory and downstream
Call/Function/Union obligations are retained in the handoff.

Original payloads are used directly: Int, Nat floatBits, List Nat bytes,
String strings/paths/characters. No CoreSyntax import, payload conversion,
supported-source restriction, source admission/readout assumption,
SourceProblem instance, actual inference transitions, or solver is supplied.
Packages remain 5/5 open and original roots 0/4 closed.
-/
namespace YulangClosure.CanonicalSourceInferenceModelR196

open OriginalSource

/-- Original source data at the first generated local obligation. -/
def literalObligation (context : Context) (site : Site) (literal : Literal) : Atom :=
  { (atom .literalDeclaration site context) with literal := some literal }

/-- Exact symbolic generation, retaining every original literal payload.
This establishes no concrete solution, source membership, or parent root. -/
theorem literal_generated_formula (context : Context) (site : Site) (literal : Literal) :
    Build context (.literal ⟨site, none⟩ literal) =
      .and (.and (.local (.atom (literalObligation context site literal))) .truth) .truth := by
  simp only [Build, sourceRules]
  rfl

#check @YulangClosure.CanonicalSourceInferenceModelR196.literal_generated_formula
#print axioms YulangClosure.CanonicalSourceInferenceModelR196.literal_generated_formula
#print YulangClosure.SourceProblem.InferenceSoundness

end YulangClosure.CanonicalSourceInferenceModelR196
