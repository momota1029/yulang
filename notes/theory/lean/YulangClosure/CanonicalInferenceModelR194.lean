import YulangClosure.OriginalSourceGeneration

/-!
R194: exact first obstruction, not a canonical inference model.

The original parent is `SourceProblem.InferenceSoundness` and its three
companion roots in `Contracts.lean`. No `SourceProblem` instance is defined.

Selected source authority: `2026-10-08-source-generalize-definition.md` §2,
selecting `2026-10-08-source-generalize-definition-and-proof.md` §§3–5.
The Literal row of §3.1 requires the actual declaration and its whole local
typed relation. L1/L2/L4 retain the independently fixed original meanings.
The research manuscript `yulang-source-type-safety-ja.tex`, `sec:all-source`,
lists “declared literal type; Return”; its opening notice does not adopt a
new original literal declaration table.

The definition below records only the *existing symbolic* generator's first
local premise. It establishes no concrete declaration, ground relation,
source typing, independent Simple-sub satisfaction, or algorithmic transition.
There are zero delivered theorem declarations.

`OriginalSourceInterpretation.LiteralDeclaration` remains a supplied relation
`Literal → ValueRow s → Prop`. Its `LiteralAtom` additionally requires the
supplied `Inputs.valueForm` and `Inputs.ground`. The corresponding
`literalKernel` and `OriginalSourceEnvironment.foldedLiteralKernel` retain
these arguments. None selects a canonical instance of them.

Stop equation: independently interpret the generated `literalDeclaration`
at the original descriptor/value/root/world and give its actual value/effect
constraints and solution readout from that declared interpretation. Defining
this by the desired Kernel atom, source typing, or assumed membership would
hide the missing meaning. This file deliberately stops before that equation.
All other accepted constructors remain in scope; none is assigned False,
removed, or given a placeholder semantic field here. Failure to locate the
fixed original declaration in the authenticated inputs is an input/registration
gap. No source-semantic contradiction or necessary new semantic choice has
been established.

The accepted `2026-10-09-native-literal-call-checking-definition.md` and its
selected `2026-10-09-native-id-original-wholearg-construction.md` §§3–8 do
fix the literal 0's `Value(Int)` / `Comp(empty,Int)` in the specified authentic
id Call frame. That bounded instance is preserved. It supplies neither an
all-literal declaration table nor the independent full-language Simple-sub
constraint encoding. No generalization of that selected case is asserted.
Its cited `2026-10-02-typed-computation-core-elaboration.md` §6 has the
literal schema `Value(type of literal)` and the Value Result/Normalize
equations. It leaves that type/declaration relation as an input, rather than
providing its total original interpretation. Inspection does not promote the
wider draft to semantic authority.

The proposed symbolic equation was:

  Build context (.literal ⟨site, none⟩ literal) =
    .and (.and (.local (.atom (literalObligation context site literal))) .truth) .truth

The single permitted check rejected its proof by `rfl`. `sourceRules` uses
well-founded recursion, so this attempted reduction was not definitional.
This proof failure is separate from the missing semantic owner. The failed
theorems were removed rather than retaining Lean's error-recovery terms.
The frozen handoff preserves their complete diagnostics and axiom output.
This final reduced artifact has not been checked again.
-/
namespace YulangClosure.CanonicalInferenceModelR194

open OriginalSource

/-- The actual first generated local premise, preserving the literal data,
source occurrence, resolved context and complete default operand fields. -/
def literalObligation (context : Context) (site : Site) (literal : Literal) : Atom :=
  { (atom .literalDeclaration site context) with literal := some literal }

end YulangClosure.CanonicalInferenceModelR194
