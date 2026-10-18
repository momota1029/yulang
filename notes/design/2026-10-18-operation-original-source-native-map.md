# Original Operation package: source/native owner map

Date: 2026-10-18  
Sprint: `operation-original-constructor-and-output-action-20261018-r14`, revision 2  
Contract SHA-256: `5998f0d8f83951acc592b2a0e689eccdeb240c9fd62df9766546066082d872f6`  
Baseline: `2a3f2a47d5013761f0e0717b0c6073c54c62d36`  
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, fixed original `c`, source domain and quantifiers unchanged; **OPEN / closure 0**  
Outcome: `source-native-evidence`; **`NO_SAFE_CODE_SLICE`** for original Operation package-field lineage

## Result

No r14 proof witness was present during this audit. The frozen prior source
owner audit still identifies the missing original input as the Operation
specialization of the original `Prim_alpha/T_alpha` projection: it must select
the already-fixed `c` at the original Written `s1` occurrence and preserve its
license and contribution through the actual complete `A_decl` output. This
audit found no native source record carrying that package or an `A_decl`
output-field action. The compiler records below are concrete, but their
identities do not establish the mathematical package fields.

The existing HIR package is a bounded syntax/source record:

- `SourceOperationDeclaration.id` is `SourceOperationId { family,
  declaration }`; the family is `SourceEffectId { module, declaration }`, and
  the operation declaration is a `SourceNodeKey`.
- It also stores spelling, visibility, name/signature source positions, source
  range, and `SourceAnnotationType` signature.
- `SourceAnnotation` stores an owning `SourceRootId`, annotation source
  position, and parsed type. A `SourceEffectRow` stores its row position,
  concrete `SourceEffectId`s, and symbolic row-variable names.

These fields identify a source declaration and its bounded parsed signature.
They do not identify the parent’s fixed semantic `c`, its original constructor
and complete telescope, `Omega/rho`, an independent field license, actual
provider/world/scope, or the output of `A_decl`. No source producer for those
original fields was located. Accordingly, I do not map any HIR field onto an
original package field.

## Traced source-to-native path

| Owner | Concrete fields and action | Boundary relative to original Operation package |
| --- | --- | --- |
| `crates/yu-hir/src/module/source_annotation.rs::declarations` (`:135`) | Registers a `SourceEffectId` from the actual module and Act declaration syntax node; records spelling, visibility, range, and later its operation declarations. It accepts only the bounded supported declaration shapes and rejects recovery/unsupported forms. | This is source family/declaration identity, not fixed `c`, the original Operation constructor, or a license. |
| `source_annotation.rs::form`, `parse_annotation`, `parse_type_source`, `parse_row` (`:317`, `:342`, `:409`, `:529`) | Retains source owner/position and parses supported primitive, variable, Function, and effect-row shapes. Concrete row names resolve to a unique `SourceEffectId`; symbolic rows retain variable names. | Parsed signature/row identity does not derive the original `A_decl` relation, its actual complete output, or a dependent governed-field action. |
| `crates/yu-solver/src/candidate_source.rs` (`:1018-1031`, `:1507`) | A resolved `LocalSourceForm::Operation` prepares candidate signature primitives and schedules `Action::Operation` with declaration, owner, source occurrence, target value endpoint, and level. | The scheduled action transports the HIR declaration and occurrence into candidate inference; it contains no original `c` witness or original output field. |
| `crates/yu-solver/src/candidate_effect.rs::candidate_operation` / `candidate_signature_value` / `candidate_signature_effect` (`:844`, `:1610+`, `:1704+`) | Recurses over the parsed Function signature and its argument/result value/effect children, constraining the candidate signature at slot 42. At the outer operation signature result-effect position, a missing row can add a candidate support view for the operation’s `SourceEffectId`; `OperationOrigin` retains declaration, occurrence, and byte accounting. | Four candidate Function children and a source-family support view are not `Prim_alpha/T_alpha`, original `c`, full source license, or its `A_decl` field action. Candidate pointer identity selects where this support view is attached; it is not an original semantic correspondence. |
| `candidate_effect.rs::candidate_signature_view`, `candidate_effect_contribution`, `candidate_check_effect_operand` (`:791`, `:987-1011`, `:1020-1078`) | A `View` retains owner, source position, allowed family IDs, optional tail, and `ViewOrigin`. A candidate `Contribution` contains only `SourceEffectId`, source origin key, and candidate-local instance. Applying a support view expands allowed members; a contribution/member against an allowance is accepted by family membership, forwarded to an open tail, or reported as a candidate mismatch. | These are candidate effect-row propagation and checking data. The `Contribution` name is not semantic `c`; no field stores `PrimLicenseContribution`, original occurrence/license, `Omega/rho`, output tuple, or `A_decl`. |
| `crates/yu-solver/src/shadow_apply.rs` (`:550-585`) and `candidate_scheme.rs` (`:1655-1659`) | Observations can expose an annotation member’s view, member index and effect ID; scheme FreshUse reads captured effect/origin and allocates a fresh candidate contribution instance. | Observation and FreshUse preserve candidate diagnostic/provenance identity. They do not authenticate original package fields or preserve an original semantic contribution through the actual declaration output. |

The source HIR owner and solver construction/consumer owners were inspected
directly. A targeted search across these owners for `Prim_Operation`,
`T_Operation`, `A_decl`, `DeclContribution`, `PrimLicenseContribution`,
`PortProv`, and `PrimOrigin` found no such source/native producer or consumer.
The concrete candidate endpoint consumer is `candidate_check_effect_operand`;
it checks candidate family inclusion/tail behavior, not an original theorem
field. No native consumer of an `A_decl`-governed Operation package field was
located.

## Exact blocker, falsifier, and next dependency

The first missing source input is the reviewed original constructor/eliminator
for the same fixed `c`, with its actual declaration/reference/substitution and
the complete original dependent fields. If its authentic case is primitive,
that input must include the real primitive introduction, origin and independent
license projection; if it is another original case, it must retain that case’s
actual route and premises. The second required input is the original field
action at the actual complete output of `A_decl`, including its output
provider/world/scope and future dependencies. Only after those are supplied
can a native source identity be mapped to a native field and followed to the
consumer checking that same field.

`NO_SAFE_CODE_SLICE` is falsified only by an accepted proof input that fixes the
original `c`, expands its actual Operation package and license, supplies its
governed field at the actual complete `A_decl` output, and gives a typed map from
those exact fields to a real source producer, propagation path, and consumer
without losing the original dependent indices or any `G/R/W/Z`, carrier/history,
admission, or future case. Family equality, `AnnotationMember`, the candidate
instance ordinal, a test injecting assumed transitions, or a green test does
not meet this condition.

Exact producer dependencies:

1. **Original Operation / complete-Sigma owner:** derive the same fixed `c`
   from the actual `Prim_alpha/T_alpha` case, including its original constructor,
   reference and substitution, and independent license. Preserve every original
   `G/R/W/Z` and domain/admission alternative.
2. **`Sigma.Lambda/A_decl` owner:** provide the actual complete output tuple and
   the lawful dependent action of that same `c` and its governed field there;
   do not substitute the request responder/provider or omit `A_decl`.
3. **Native source owner, after (1) and (2):** identify the source constructor
   and exact native field corresponding to that accepted proof input, then
   trace it through candidate construction/propagation to an actual consumer.
   This is a requested dependency, not current write authority.

No test, build, compiler edit, or runtime was run. Historical implementation
tests establish only their recorded bounded annotation/effect-row behavior and
do not supply this witness. The original theorem remains **OPEN / closure 0**;
no source domain, diagnostics, semantic expectation, or inference behavior is
changed. There is no provisional code instrumentation to clean up and no
scratch path was created.

## Prior evidence reused and rejected

- Reused the independently reviewed r13 source/native map
  `notes/design/2026-10-18-choose-primitive-license-source-native-map.md`
  (SHA-256 `9761cfbbc9fc2ecba8ec23027db8e6e37e8614a13b4fcffe0e350d256c648a5c`)
  for the source annotation, candidate effect and actual consumer ownership
  trace. Its exact distinction between family identity and semantic contribution
  remains valid; this audit did not find a new proof field to extend it with.
- Reused `notes/theory/2026-10-18-npair-original-operation-field-supplier.md`
  as prior owner-level evidence for the unresolved same-`c` Operation
  projection and actual `A_decl` output. It is a source-owner audit, not closure
  of that missing input.
- Rejected the unadopted `OperationWritten(q)` / `OC-Written-Out` proposal as
  an original constructor or native source producer. It does not identify the
  already-fixed `c`; relabeling it would introduce a new semantic identity.
- Accounted for fixed-`c` candidate
  `notes/design/2026-10-18-operation-fixed-c-specialization-candidate.md`
  (SHA-256 `b873c10a55b91c1a7d6caf9736b3dbe10bee0499edfc98e4ff512ed222f84322`),
  contribution formation proposal
  `notes/design/2026-10-18-operation-contribution-formation-proposal.md`
  (SHA-256 `7d966d665fc4a87806c4ba989bb11c8ec1fbde34a39432a31e190cf207ec1236`),
  adoption decision (SHA-256
  `da4309a9e00ed136ac80ade55d7140dcd201ecd3ea8ea98bcad9649649cfa783`), and
  compatibility audit (SHA-256
  `30e6c9604f5d848ca4998295eced4acb158844944ca77982f2e82ff9b8341672`) as
  prior candidate/negative evidence only. Its new selector/output action,
  R/W/Z schemas and consumer-equivalence premises are not derived here and do
  not define an implemented or authoritative source rule.
- Rejected HIR source IDs, signature support, family membership, candidate
  `Contribution` instances and `FreshUse` observations as substitutes for the
  original package or its license/output action. They are real candidate
  records but lack the required theorem fields.

Direct source locators inspected: `source_annotation.rs:48-63,135+,317-359,
409-529`; `candidate_source.rs:1018-1031,1507`; `candidate_effect.rs:148-204,
791+,844+,987-1078,1610+,1704+`; `candidate_scheme.rs:1655-1659`;
`shadow_apply.rs:550-585`. Direct dependencies and artifact hashes are frozen
in the paired inbox handoff.
