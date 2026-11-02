import YulangClosure.PaperExecutionSyntax
import YulangClosure.CanonicalSourceInferenceModelR196

/-!
R236 models the direct canonical-literal path rather than R232's reciprocal
bounds or R235's quotient-only leaf. The generated descriptor is a canonical
Paper type constant selected by the original raw literal. The output retains
the exact source site, payload, root, event, scope and witness supplied to it.

This is a candidate generator equation for the adopted L1 rule. It does not
interpret the full SimpleSub.Term algebra, source effect permissions, arbitrary
solver assignments, or construct a complete SourceProblem instance. The
original symbolic Build consumer is included so the actual literal payload
feeding this map is explicit.
-/
namespace YulangClosure.CanonicalLiteralGeneratorR236

open OriginalSource

def toPaperLiteral : OriginalSource.Literal → PaperTypes.Literal
  | .unit => .unit
  | .bool value => .boolean value
  | .int value => .integer value
  | .floatBits bits => .floatBits bits
  | .string value => .string value
  | .bytes bytes => .bytes bytes
  | .path path => .path path
  | .character grapheme => .character grapheme

def baseType : OriginalSource.Literal → PaperTypes.Base
  | .unit => .unit
  | .bool _ => .bool
  | .int _ => .int
  | .floatBits _ => .float
  | .string _ => .string
  | .bytes _ => .bytes
  | .path _ => .path
  | .character _ => .char

/-- Direct literal generation returns a canonical constant, without allocating
a variable that must be solved to equal that constant. -/
def generateType (literal : OriginalSource.Literal) : PaperTypes.Ty :=
  .base (baseType literal)

def generateValue (literal : OriginalSource.Literal) : PaperTypes.Value :=
  .literal (toPaperLiteral literal)

structure Generated (Root Event Scope Witness : Type) where
  site : OriginalSource.Site
  literal : OriginalSource.Literal
  descriptor : PaperTypes.Ty
  value : PaperTypes.Value
  root : Root
  event : Event
  scope : Scope
  witness : Witness

def generate {Root Event Scope Witness : Type}
    (site : OriginalSource.Site) (literal : OriginalSource.Literal)
    (root : Root) (event : Event) (scope : Scope) (witness : Witness) :
    Generated Root Event Scope Witness :=
  ⟨site, literal, generateType literal, generateValue literal,
    root, event, scope, witness⟩

/-- Consume the exact source atom emitted by the original Build node. The
payload witness is ordinary data carried by that atom, not a source typing or
solver premise. -/
def generateFromAtom {Root Event Scope Witness : Type}
    (atom : OriginalSource.Atom) (literal : OriginalSource.Literal)
    (payload : atom.literal = some literal)
    (root : Root) (event : Event) (scope : Scope) (witness : Witness) :
    Generated Root Event Scope Witness :=
  generate atom.site (atom.literal.get (by simp [payload]))
    root event scope witness

theorem generateType_matches_adopted_l1 (literal : OriginalSource.Literal) :
    generateType literal = PaperTypes.literalType (toPaperLiteral literal) := by
  cases literal <;> rfl

theorem generateValue_matches_adopted_l1 (literal : OriginalSource.Literal) :
    generateValue literal = PaperTypes.Value.literal (toPaperLiteral literal) := rfl

theorem generate_preserves_coordinates {Root Event Scope Witness : Type}
    (site : OriginalSource.Site) (literal : OriginalSource.Literal)
    (root : Root) (event : Event) (scope : Scope) (witness : Witness) :
    let result := generate site literal root event scope witness
    result.site = site ∧ result.literal = literal ∧ result.root = root ∧
      result.event = event ∧ result.scope = scope ∧ result.witness = witness := by
  simp [generate]

/-- The actual original symbolic source generator emits this payload-bearing
literal declaration node; no source typing or solver result is assumed. -/
theorem original_build_consumes_literal_payload
    (context : OriginalSource.Context) (site : OriginalSource.Site)
    (literal : OriginalSource.Literal) :
    let atom := CanonicalSourceInferenceModelR196.literalObligation context site literal
    atom.literal = some literal := by
  rfl

theorem original_build_literal_formula
    (context : OriginalSource.Context) (site : OriginalSource.Site)
    (literal : OriginalSource.Literal) :
    Build context (.literal ⟨site, none⟩ literal) =
      .and (.and (.local (.atom
        (CanonicalSourceInferenceModelR196.literalObligation context site literal))) .truth) .truth :=
  CanonicalSourceInferenceModelR196.literal_generated_formula context site literal

/-- Compose the actual Build literal atom with the direct canonical generator.
This is an application at the original source-generation leaf; semantic
admission and arbitrary-solution interpretation remain separate obligations. -/
theorem original_build_atom_generates_canonical_result
    {Root Event Scope Witness : Type}
    (context : OriginalSource.Context) (site : OriginalSource.Site)
    (literal : OriginalSource.Literal) (root : Root) (event : Event)
    (scope : Scope) (witness : Witness) :
    let atom := CanonicalSourceInferenceModelR196.literalObligation context site literal
    let result := generateFromAtom atom literal (by rfl) root event scope witness
    result.site = site ∧ result.literal = literal ∧
      result.descriptor = PaperTypes.literalType (toPaperLiteral literal) ∧
      result.value = PaperTypes.Value.literal (toPaperLiteral literal) ∧
      result.root = root ∧ result.event = event ∧
      result.scope = scope ∧ result.witness = witness := by
  simp [generateFromAtom, generate,
    CanonicalSourceInferenceModelR196.literalObligation,
    OriginalSource.atom, generateType_matches_adopted_l1,
    generateValue_matches_adopted_l1]

/-- End-to-end connection for the literal source-generation node: the original
Build equation emits the payload-bearing atom, and consuming that exact atom
produces the canonical L1 type/value while retaining all supplied coordinates.
This still does not derive the Kernel premise from an arbitrary Simple-sub
solution or close the whole SourceProblem parent. -/
theorem original_build_generator_connection
    {Root Event Scope Witness : Type}
    (context : OriginalSource.Context) (site : OriginalSource.Site)
    (literal : OriginalSource.Literal) (root : Root) (event : Event)
    (scope : Scope) (witness : Witness) :
    Build context (.literal ⟨site, none⟩ literal) =
      .and (.and (.local (.atom
        (CanonicalSourceInferenceModelR196.literalObligation context site literal))) .truth) .truth ∧
    (let atom := CanonicalSourceInferenceModelR196.literalObligation context site literal
     let result := generateFromAtom atom literal (by rfl) root event scope witness
     result.site = site ∧ result.literal = literal ∧
       result.descriptor = PaperTypes.literalType (toPaperLiteral literal) ∧
       result.value = PaperTypes.Value.literal (toPaperLiteral literal) ∧
       result.root = root ∧ result.event = event ∧
       result.scope = scope ∧ result.witness = witness) := by
  exact ⟨original_build_literal_formula context site literal,
    original_build_atom_generates_canonical_result context site literal root event scope witness⟩

#check @generateType_matches_adopted_l1
#print axioms generateType_matches_adopted_l1
#check @generateValue_matches_adopted_l1
#print axioms generateValue_matches_adopted_l1
#check @generate_preserves_coordinates
#print axioms generate_preserves_coordinates
#check @original_build_consumes_literal_payload
#print axioms original_build_consumes_literal_payload
#check @original_build_literal_formula
#print axioms original_build_literal_formula
#check @original_build_atom_generates_canonical_result
#print axioms original_build_atom_generates_canonical_result
#check @original_build_generator_connection
#print axioms original_build_generator_connection
#print YulangClosure.SourceProblem.InferenceSoundness

end YulangClosure.CanonicalLiteralGeneratorR236
