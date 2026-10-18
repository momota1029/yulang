# Operation licensed-field source producer map

Status: frozen producer design, revision 1; no code or test authority. This is a
source-owner map for r16's **research semantics v1 candidate**, not evidence
that this rule existed in the prior semantics, preserves old behavior, or
closes `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`. The parent remains
OPEN / closure 0. The rule draft was not present when this map was frozen, so
the concrete rule fields and its exact evidence type remain a Luna-owned input.

Assignment: `OP-LICENSED-FIELD-SOURCE-PRODUCER-20261018-R16`, revision 1.
Contract: `tasks/agent-loop/sprints/operation-licensed-field-rule-and-source-producer-20261018-r16.md`,
SHA-256 `ce65e0b259c3a4af6087449a0ecafc5f539f8662d8d63b04defdb02349b7dc0b`.
Parent gate: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`.

## Source-to-consumer map

The required future route is:

```text
source operation declaration / annotation occurrence
  -> HIR source occurrence and exact declaration owner
  -> source field j and positive Written field, if the accepted rule identifies one
  -> independently sourced field-license evidence
  -> semantic identity for the existing fixed c
  -> candidate view/member or Contribution
  -> Capture and actual FreshUse remapping
  -> candidate propagation and the actual effect consumer
```

The first three semantic steps cannot yet be filled by naming a proposed rule
constructor. The rule file was absent, and the r14/r15 evidence says the old
fixed-`c` field/license/output producer is still missing. In particular, no
mapping from an observed output family member back to the original `c` is
accepted. A later mapping must retain the same formed `c`, actual positive
Written field ordinal `j`, independent license, complete-output field after
`A_decl`, and all binders required by the reviewed rule. A response field,
predecessor field, result-family equality, or newly allocated `c*` does not
fill this edge.

| Stage and current owner | Existing evidence | What it does not supply |
| --- | --- | --- |
| Source declaration and signature: `yu-hir/src/module/source_annotation.rs::declarations`, `form`, `parse_annotation`, `parse_type`, `parse_row` | `SourceOperationDeclaration` retains family/declaration IDs, spelling, visibility, declaration/name/signature positions and a parsed `SourceAnnotationType`. A `SourceEffectRow` retains its row position, concrete `SourceEffectId`s and symbolic variables. | No separate field-license object, original contribution `c`, positive Written classification, output action, or operation-field ordinal-to-license association is represented here. The supported grammar is nullary operation declarations with ordinary source effect rows. |
| Source occurrence and scheduling: `yu-hir/src/module/local_source.rs` and `yu-solver/src/candidate_source.rs::Action::Operation` scheduling / action dispatch | HIR retains the local source occurrence and resolved declaration. The solver action carries declaration, source owner, occurrence, target endpoint and level into `candidate_operation`. | It carries no independent field-license witness and no complete `A_decl` output field correspondence. It is a candidate inference input, not the original semantic formation derivation. |
| Candidate signature/operation construction: `candidate_effect.rs::candidate_operation`, `candidate_signature_value`, `candidate_signature_effect`, `candidate_signature_view`, `candidate_effect_contribution` | Recursively builds value/effect constraints. `View` stores source owner/position, allowed family IDs, optional tail, and `ViewOrigin`; operation provenance retains declaration and occurrence. `Contribution` stores a `SourceEffectId`, source origin key and candidate-local instance. The operation family support is attached separately from members parsed in the signature. | These fields identify candidate family/member shape and origin. They are not the new independent license and do not identify the original fixed `c`, its original formation, or the licensed `j` at the actual completed output. Family ID, member ordinal, tail, and candidate instance must stay distinct from rule evidence. |
| Propagation/consumer: `candidate_effect.rs::candidate_check_effect_operand` and its bound/extrusion callers | A Support view is expanded into member operands plus its tail; `AnnotationMember(view,j)` can retain the view/member observation. Contribution operands follow their existing candidate checks. | Current checking is family/member/tail constraint behavior. It is not an Operation licensed-field consumer until it receives and checks the rule's independent license and fixed-`c` identity. Which accepted programs or diagnostics change depends on the frozen v1 rule and must be made explicit there. |
| Capture and fresh use: `candidate_scheme.rs::Capture` handling, `candidate_remapped_effect_view`, FreshUse construction and replay | Capture retains candidate graph evidence. FreshUse remaps a candidate view and preserves an `AnnotationMember`'s member ordinal; contribution copying creates a candidate contribution with copied family and origin. | These are candidate transport maps. They do not prove that the source license is captured, that the same semantic `c` survives, or that a copied member retains the rule's field/license association. Any new proof-relevant association must be included in Capture and every actual FreshUse route, or fail closed. |
| Borrowed observation: `shadow_apply` candidate effect operand projection, `CandidateGraphFreshUse` | Exposes actual candidate annotation member/support provenance and current FreshUse observations. | It observes the candidate graph; it neither issues a license nor establishes original `c` or complete-output correspondence. It cannot serve as an injected desired transition. |

The **existing candidate member fields** are (a) `View.allowed` family IDs,
`View.tail`, source owner/position and provenance; (b) the `AnnotationMember`
view/member pair; and (c) `Contribution.effect`, `.origin`, and candidate
`.instance`. The **new evidence** must be the rule's independently produced
field-license evidence joined to the pre-existing semantic identity of `c` and
the actual field occurrence. The new evidence cannot be represented by
relabeling any existing family, ordinal, origin, instance, or FreshUse ID.

## Source-language edge still open

The inspected HIR type contains only Unit/Int/Bool/Str/variable/Function and
optional effect rows; a row contains concrete effect IDs or variables. There is
no source syntax or typed-HIR field for an independent license reference or
original `c` formation. The current source owner can establish that a concrete
family name appears at a specific annotation position. It cannot establish
that this name licenses one exact positive Written field of an existing `c`.

Therefore the source-producer path is conditional on the frozen semantic rule
showing an independently meaningful license is derivable from an existing
source construct. If it instead requires data absent from syntax/HIR, that is
the exact missing edge: **source syntax/typed HIR -> independent field-license
evidence for `(fixed c, positive Written j)`**. Luna must decide whether the
candidate requires a versioned source-syntax/HIR extension and an authority
revision. This packet does not invent that evidence or edit those owners.

## Proposed vertical fixture and assertion contract

Smallest existing source shape to carry into the approved design is:

```yu
act tick:
    our next: () -> [tick] int

my lookup = tick::next
my use: () -> [tick] int = lookup
```

This is only a **proposed fixture shape**. Under current HIR it supplies an
operation declaration, one nested positive result-effect row, the concrete
family member and a resolved source lookup/use. It does not currently supply
the separate license evidence or original `c`; it is not yet an executable
test contract for v1.

Once the rule is frozen and its producer edge exists, the required single
vertical assertion is that solving this same source fixture emits exactly one
proof-relevant licensed-field record for the exact declaration/occurrence,
existing fixed `c`, positive result-effect `j`, independent license and final
same-`c` field after the complete output action; Capture and one actual
FreshUse preserve that identity; and the actual candidate consumer accepts the
licensed member while rejecting a same-family sibling lacking that license.
The assertion must inspect emitted evidence and the consumer result in the
same execution. It must not seed a record, synthesize a transition, compare
only family IDs, or infer a license from a green solve. If the rule specifies
different source syntax or consumer behavior, update the fixture only after
the semantic artifact is frozen and independently reviewed.

## Observable behavior and future code seam

The likely behavior seam is candidate effect checking. A newly recognized
licensed field can change whether an existing candidate member propagates or
satisfies a consumer check; an unlicensed same-family sibling may stop being
accepted. Any current error/conflict diagnostic at that boundary may therefore
change, disappear, or be replaced by the rule's missing-license failure. The
exact diagnostic and acceptance matrix is a required row in the Luna-owned
rule's compatibility table. No expectation or diagnostic should be changed
before that table is fixed.

If the rule and source producer pass independent review, a **separate exact
code lease** should name at least these owners/functions, limited to the
necessary subset:

1. `crates/yu-solver/src/candidate_effect.rs`: `candidate_operation`,
   `candidate_signature_value`, `candidate_signature_effect`,
   `candidate_signature_view`, `candidate_check_effect_operand`, and any
   contribution allocation/propagation function the frozen rule actually
   needs. This is where source rule evidence joins the candidate constraint
   and is consumed.
2. `crates/yu-solver/src/candidate_scheme.rs`: Capture of the new evidence,
   `candidate_remapped_effect_view`, actual FreshUse construction/replay, and
   the copy path for any new Contribution-linked record. This is where the
   rule identity must survive copying.
3. `crates/yu-solver/src/shadow_apply.rs`: only the borrowed projection needed
   to assert the real emitted evidence and observe its same-execution consumer
   effect. It must not become an alternate producer.

HIR currently has no independently licensed-field source. If the final rule
requires adding one, `crates/yu-hir/src/module/source_annotation.rs`,
`crates/yu-hir/src/module/local_source.rs`, their owning HIR module wiring and
the source-to-solver `candidate_source.rs` route are additional exact owners;
they are outside the current three-file conditional code scope. Return to Luna
for the rule/dependency/lease revision before touching them. No production code
or test path is leased by this assignment.

## Prior evidence and falsifiers

Reused as owner/candidate evidence: r14's source-native map and source hashes;
r15's inverse construction failure and exact same-fixed-`c` missing projection;
the fixed-c candidate and adoption/compatibility records. Existing HIR and
candidate source paths are reused only to locate identities and current
behavior. Rejected as license or original `c` evidence: family membership,
candidate `Contribution`, `AnnotationMember`, support view, origin key,
tail, candidate instance, Capture/FreshUse identity and row equality. None
closes a parent premise.

Falsifiers for the future producer/consumer slice:

- license or `c` is reconstructed from family equality, member position,
  origin, or a newly allocated candidate instance;
- the rule evidence is absent from actual accepted source HIR or comes from a
  test-injected adapter;
- evidence describes a response/predecessor field instead of the actual
  complete output after `A_decl`;
- the `j` or its polarity changes across Capture/FreshUse without a recorded
  rule-authorized mapping;
- consumer behavior accepts an unlicensed sibling, or the runtime assertion
  checks only a borrowed observation rather than the actual consumer;
- changed W/Z, reference/composite, pending/divergent, future or consumer
  cases are omitted from the semantic rule while claiming the unchanged parent.

No provisional instrumentation is proposed: the source evidence edge is not
yet constructible from the current HIR model. Cleanup owner is therefore not
applicable.
