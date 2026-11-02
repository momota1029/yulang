# R236 primary model construction handoff

Contract: `tasks/agent-loop/sprints/canonical-literal-generator-r236.md`,
SHA-256 `7634fc2a05d01fb33fa36974296850e7946b526566937cb21e47fa77393f4f00`.
Baseline: pushed `52c8053d5` on `yulang3`. Unchanged parent:
`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128–130`.

## Frozen construction

Module `notes/theory/lean/YulangClosure/CanonicalLiteralGeneratorR236.lean`
is frozen at SHA-256
`9564501e59b8f595a4630e812728412efc0e213c1281e4a899a16fe8efef235c`.

It maps each payload-preserving `OriginalSource.Literal` to the matching
`PaperTypes.Literal`, produces a direct canonical `PaperTypes.Ty.base` and
literal value, and retains the supplied original site, root, event, scope and
witness. It consumes the exact payload-bearing atom from R196's original
symbolic `Build` literal node. No reciprocal constraints or quotient readout
are used.

Checked declarations and complete printed types:

```lean
generateType_matches_adopted_l1 (literal : OriginalSource.Literal) :
  generateType literal = PaperTypes.literalType (toPaperLiteral literal)
-- axioms: []

generateValue_matches_adopted_l1 (literal : OriginalSource.Literal) :
  generateValue literal = PaperTypes.Value.literal (toPaperLiteral literal)
-- axioms: []

generate_preserves_coordinates {Root Event Scope Witness : Type}
  (site : OriginalSource.Site) (literal : OriginalSource.Literal)
  (root : Root) (event : Event) (scope : Scope) (witness : Witness) :
  let result := generate site literal root event scope witness
  result.site = site ∧ result.literal = literal ∧ result.root = root ∧
    result.event = event ∧ result.scope = scope ∧ result.witness = witness
-- axioms: [propext]

original_build_consumes_literal_payload
  (context : OriginalSource.Context) (site : OriginalSource.Site)
  (literal : OriginalSource.Literal) :
  let atom := R196.literalObligation context site literal
  atom.literal = some literal
-- axioms: []

original_build_literal_formula
  (context : OriginalSource.Context) (site : OriginalSource.Site)
  (literal : OriginalSource.Literal) :
  Build context (.literal ⟨site, none⟩ literal) =
    .and (.and (.local (.atom (R196.literalObligation context site literal))) .truth) .truth
-- axioms: [propext, Classical.choice, Quot.sound]

original_build_atom_generates_canonical_result
  {Root Event Scope Witness : Type}
  (context : OriginalSource.Context) (site : OriginalSource.Site)
  (literal : OriginalSource.Literal) (root : Root) (event : Event)
  (scope : Scope) (witness : Witness) :
  let atom := R196.literalObligation context site literal
  let result := generateFromAtom atom literal ⋯ root event scope witness
  result.site = site ∧ result.literal = literal ∧
    result.descriptor = PaperTypes.literalType (toPaperLiteral literal) ∧
    result.value = PaperTypes.Value.literal (toPaperLiteral literal) ∧
    result.root = root ∧ result.event = event ∧ result.scope = scope ∧
    result.witness = witness
-- axioms: [propext]

original_build_generator_connection
  {Root Event Scope Witness : Type}
  (context : OriginalSource.Context) (site : OriginalSource.Site)
  (literal : OriginalSource.Literal) (root : Root) (event : Event)
  (scope : Scope) (witness : Witness) :
  Build context (.literal ⟨site, none⟩ literal) =
    .and (.and (.local (.atom (R196.literalObligation context site literal))) .truth) .truth ∧
  (let atom := R196.literalObligation context site literal
   let result := generateFromAtom atom literal ⋯ root event scope witness
   result.site = site ∧ result.literal = literal ∧
     result.descriptor = PaperTypes.literalType (toPaperLiteral literal) ∧
     result.value = PaperTypes.Value.literal (toPaperLiteral literal) ∧
     result.root = root ∧ result.event = event ∧ result.scope = scope ∧
     result.witness = witness)
-- axioms: [propext, Classical.choice, Quot.sound]
```

The pinned checker rebuilt the module successfully and its named type/axiom
audits passed for all seven declarations. Lean `4.35.0`, Lake
`5.0.0-src+eb6cafb`. The module directly uses the `R196` symbolic Build
equation, whose axiom set is inherited only by the two Build-connection
theorems.

## Parent application and authority boundary

This is a concrete direct literal generator candidate consumed at the actual
symbolic Build node. It proves the all-eight source-payload-to-Paper-literal
map, canonical L1 type/value equations, and retention of caller-supplied
coordinates. It does **not** establish that the all-eight direct constants
are the selected Yulang algorithm's authorized generation equation; fresh
review is pending on that point.

It also does not define the full `SimpleSub.Term` interpretation, construct
the adopted intrinsic-effect/pure-Return carrier, derive the original
`LiteralAtom` from every arbitrary solver assignment, preserve distinct
synthesis/written-target/final-root descriptors through actual source
typing, or produce a concrete `SourceProblem.sameScoped` witness. The
generator receives root/event/scope/witness as inputs; their authenticity in
the original model is not proved. No theorem is applied to
`SourceProblem.InferenceSoundness`; parent-premise delta remains **0**, roots
**0/4**. No semantics or source forms are changed.

## Resources and review

Awaiting one fresh nonauthor `spec_auditor` review of the exact contract,
module, L1 adoption, top-level algorithm, pinned paper literal branch and R196
Build consumer. Review must decide whether this direct all-eight candidate is
source-authorized and whether the remaining parent edge is stated accurately.
It cannot certify whole-language soundness.

Existing `.lake` was 134,587,836 bytes before R236 checking and 144,880,556
after: growth **10,292,720 bytes**, within the 64 MiB cap. No new cache path,
worktree, environment or target was created. No Rust/Cargo or general tests
ran. Unrelated dirty files and UNKNOWN/quarantined paths remain untouched.
