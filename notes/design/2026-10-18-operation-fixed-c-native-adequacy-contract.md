# Fixed-c Operation interpretation: native adequacy contract

Date: 2026-10-18  
Sprint: `operation-fixed-c-complete-interpretation-20261018-r15`, revision 1  
Contract SHA-256: `9037ea47c38c28b692ecf3ffe0ccfe6a70f7276c854459ea9831a2ddebc748e7`  
Baseline declared by contract: `2a3f2a47d5013761f0e0717b0c6073c54c62d36`  
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, original fixed `c`, source domain and quantifiers unchanged; **OPEN / closure 0**.  
Outcome: `source-native-evidence`; **`NO_SAFE_CODE_SLICE`**.

## Finding

The r15 candidate's proof-relevant records do not correspond to a complete native witness for the original fixed `c`. The current source path retains source declaration identity, signature positions, family IDs, candidate support/member identity, some operation provenance, and copied view/member identity through FreshUse. It has no producer for the candidate's fixed `c`, its independent field license, or its field action at the actual complete `A_decl` output. Its actual local effect consumer checks candidate family membership/tail behavior. No native consumer of the original `A_decl`-governed package field was found.

This is the same bounded obstruction established by the reviewed r14 map and constructor attempt, with the r15 candidate's complete field list compared against the concrete owners below. It is not a global non-derivability result and does not refute the parent theorem. No candidate-to-native semantic correspondence is claimed.

## Frozen inputs and hash reconciliation

The required r14 map and handoff match their pins exactly:

- `notes/design/2026-10-18-operation-original-source-native-map.md`: `8cfc7e17950af18ac1370aadb978055b020cb2e5414558d45e62e3994994ccb1`.
- `tasks/agent-loop/inbox/20261018-operation-original-source-native-map.md`: `29dc760863fc18cfd7653ee4675272c2c2db3e33dc0ccb4003926b2eb669e0ac`.

The current source-owner bytes also match the r14 handoff pins: `source_annotation.rs` `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f`; `candidate_source.rs` `1a65c7afb02a4afd538a34c34086108959579e06aafe8fbcab8ad6a6b3a65f3e`; `candidate_effect.rs` `3fbce03f3d96b9a719bfa4bc4203c6b6fc3b4903c91104f4a50a4627ad1de75c`; `candidate_scheme.rs` `03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd`; `shadow_apply.rs` `eb0b9dcd8529e067ec8778c7888f3595ad8df466e1be4243b1d2104c853952d7`.

Candidate/adoption inputs, reconciled to r15:

- Fixed-c candidate `notes/design/2026-10-18-operation-fixed-c-specialization-candidate.md`: `b873c10a55b91c1a7d6caf9736b3dbe10bee0499edfc98e4ff512ed222f84322`.
- Formation proposal `notes/design/2026-10-18-operation-contribution-formation-proposal.md`: `7d966d665fc4a87806c4ba989bb11c8ec1fbde34a39432a31e190cf207ec1236`.
- Adoption decision `notes/design/2026-10-18-operation-contribution-adoption-decision.md`: `da4309a9e00ed136ac80ade55d7140dcd201ecd3ea8ea98bcad9649649cfa783`.
- Compatibility analysis `notes/theory/2026-10-18-operation-original-formation-compatibility.md`: `30e6c9604f5d848ca4998295eced4acb158844944ca77982f2e82ff9b8341672`.
- r14 original constructor witness: `notes/design/2026-10-18-operation-original-constructor-witness.md`, `1735a15850e6d7d10218b206afade085f10ed7b5b1eddfbef63a9926f85dcd16`; parent application `notes/theory/2026-10-18-operation-original-output-field-action.md`, `1a14ba8ce80c5f369e549315acdcb098c3825c9a66fbff0537f9e28dba7b9401`.

The source-owner map's independently reviewed PASS is evidence about these bounded source fields, not about original semantic fields. The r14 proof and source/spec reviews both report zero original conditions closed. No moving r15 proof artifact is imported here.

## Candidate-field to owner correspondence

The fixed-c candidate proposes a formation-time selector payload `q` for an already fixed contribution `c`, then an output action at the actual complete result of `A_decl`. Its proposed proof data and the actual native records compare as follows.

| Candidate field or proof datum | Actual source/native record | Status |
| --- | --- | --- |
| Original declaration `p`, `alpha`, actual clause/registration and `Ref(t,m_v)` at `v` | `SourceOperationId { family: SourceEffectId { module, declaration }, declaration: SourceNodeKey }`; declaration lookup retains the family/declaration identity and spelling/visibility. `SourceOperationDeclaration` retains name/signature positions, range and parsed signature. `Action::Operation` carries the resolved declaration and its expression occurrence. | Partially represented as source declaration and use identity. It is not the original semantic constructor/reference derivation or its typed substitution. |
| Joint `theta`, complete `Sigma_theta=(A,B,Lambda)` and original scope/binder tree | Bounded `SourceAnnotationType` tree (`Unit/Int/Bool/Str/Variable/Function`) and effect rows; solver-local signature recursion maps these into candidate terms. | No original joint assignment, complete dependent telescope, or original binder lineage is carried. |
| `d_form`: formation proof of the already fixed `c` | No `c` field or original formation term exists on HIR `SourceOperationDeclaration`, `Action::Operation`, `OperationOrigin`, `View`, `Contribution`, or `FreshUse` effect operands. | Newly absent. No producer located. |
| `kappa_c`: same-`c` local Operation-introduction provenance and original license | `OperationOrigin` retains the HIR declaration `Arc`, expression occurrence and retained-byte count; the enclosing `View` retains the root owner. `ViewOrigin::Operation` retains that origin for operation signature views. | Declaration/use provenance is preserved, but it is not `kappa_c`, an original semantic `c`, or a license witness. |
| `b_out`: original output binder after the complete `A_decl` development | No output-binder identity or complete `A_decl` derivation is carried in the Operation action or effect view. | Newly absent. |
| `(s1,j,a)`: positive Written result-effect occurrence and its operand | HIR parser retains `SourceNodeKey` positions for signature and row syntax; `SourceEffectRow` holds concrete `SourceEffectId`s and symbolic variables. Candidate `View` retains owner, position, allowed IDs and optional tail; `AnnotationMember(view,j)` has a member index and resolves to an allowed family ID. | Syntax row/member positions and operand family IDs are represented. `j` is an index into candidate `allowed`, not proof of semantic occurrence `s1` for `c`. Equal family/operand IDs do not identify distinct source occurrences or semantic witnesses. |
| `ell_field`: independently valid field license at `(s1,j)` | No license field in parsed annotations, operation provenance, support views, members, contributions or FreshUse maps. | Newly absent. It cannot be inferred from source position, family equality or a typed signature alone. |
| Actual complete `d_A`, `out(d_A)=(r_out,Cout)`, `sigma_out`, `beta_out`, and `field_projection` | Candidate signature conversion reads the parsed declaration signature. It does not execute or represent the original `A_decl` suffix, complete output tuple, output provider/world, dependent substitution, or output typing proof. | Newly absent. No source field or output action is carried. |
| `lambda_out`, final `G/K/D`, output license/domain/future action | Candidate `View.tail` and row propagation are candidate inference data. They are not original provider/world/scope/admission/future certificates. | No original dependent action. |
| `eta_c`: same original `c` contributes to the projected field at the actual output | Candidate `Contribution` is `{ effect: SourceEffectId, origin: SourceNodeKey, instance: candidate-local ordinal }`; no `c`, field license, or `A_decl` output occurs in it. | Newly absent. No native producer or corresponding actual consumer. |

The source parser's row position and candidate member index are useful provenance. They must remain distinct from the original semantic occurrence, fixed contribution identity and independent license. The r15 candidate's `SameOwner` premise explicitly compares full source introduction, reference, joint `theta`, binder and occurrence; the native declaration ID/family and `OperationOrigin` do not establish that premise.

## Actual source-to-constraint-to-propagation path

1. `crates/yu-hir/src/module/source_annotation.rs::declarations` registers an effect family and its operation declarations from module syntax. `form`, `parse_annotation`, type parsing and row parsing retain owner/positions and supported type/effect-row shapes. Operation lookup resolves a source family/name to the declaration record; it does not form the original semantic `c` or its license.
2. `crates/yu-solver/src/candidate_source.rs` sees `LocalSourceForm::Operation { Resolved(declaration) }`, prepares signature primitives, emits the ordinary value/effect facts, and schedules `Action::Operation { declaration, owner, occurrence, target, level }`.
3. `candidate_effect.rs::candidate_operation` recursively constrains the parsed signature and links the candidate operation target at slot 42. Its nested Function result-effect path calls `candidate_signature_effect`; where the row is present, a `View` retains the row's source position, allowed effect-family IDs and tail. For an absent row, the operation family can be attached as a candidate `Support(view)` only at the pointer-identical root operation Function result effect (`std::ptr::eq(ty, &declaration.signature)`). That root intrinsic support is not the nested positive Written field `s1`.
4. `candidate_check_effect_operand` is the concrete candidate effect-consumer: Support expands into queued `AnnotationMember(view,j)` checks plus its tail; Contribution or AnnotationMember against an Allowance is accepted by family membership, forwarded to an open tail, or reported as a candidate mismatch; a contribution/member against EmptyNegative mismatches. This checks candidate effect inclusion. It does not consume `eta_c`, inspect a semantic field license, apply `A_decl`, select/remove the original contribution, or establish original Contrib/Inc/Cover behavior.
5. `shadow_apply` observations expose candidate annotation member view/index/effect. `candidate_scheme.rs::prepare_candidate_fresh_use` copies effect endpoints: Support/Allowance views are remapped, AnnotationMember retains its numeric member index on the remapped view, and Contribution is separately reallocated from its effect ID and origin. The remap cache is keyed by `(view_id, mapped_tail)` within a FreshUse; signature parsing also memoizes candidate views by source row `SourceNodeKey`. Operation views have `ViewOrigin::Operation` and no annotation source-weight payload. These identity mechanisms preserve candidate graph/cache lineage. They do not add `b_out`, original `c`, `ell_field`, or the original output action to Capture/FreshUse.

Thus the actual consumer seam is real but has a different judgment and operands than the candidate's parent consumer obligations. A test that injects a presumed `eta_c` or assumed transition would bypass the missing producer and would not demonstrate source/native adequacy.

## Existing test and proof evidence

Read-only inspection of `crates/yu-hir/tests/operation_source.rs`, `crates/yu-solver/tests/candidate_operation_source.rs`, and the relevant operation/effect cases in `candidate_effect_annotation.rs` confirms the bounded behavior already covered: HIR resolves the actual declaration and preserves family/declaration identity, spelling, visibility, signature tree and source/use positions; candidate tests check lookup without forming a call, signature/value constraints, aliases, prepended operation-family support, original interface member ordinals, and rejection of a foreign effect family. These tests do not construct the original fixed `c`, independent field license, complete `A_decl` output, or semantic consumer judgment. They are historical implementation evidence only; none was run for this assignment.

The r14 constructor witness is the relevant failed proof attempt: it tried primitive and composite packaging and found the independent original license/field-law argument missing. Its paired parent application records no `d_c`, `eta_c`, or parent progress. The reviewed r14 map independently establishes the native owner boundary. Neither result is a theorem of non-derivability.

## Reused evidence, exclusions and TODO owners

Reused: the r14 source/native map and its PASS review; the r14 original-constructor attempt and parent application as the bounded proof-side failure; r15's frozen candidate, formation proposal, adoption decision and compatibility analysis as candidate/negative evidence. The r14 proof found no authentic same-`c` constructor projection, independent license, or complete `A_decl` output-field action; it did not prove non-derivability. The adoption decision rejects treating a fresh additive `OperationWritten(q)` as the old fixed `c`. The fixed-c candidate expressly introduces `Op-Fixed-Select` and `Op-Fixed-Out` unless exact existing rules derive them; they are not current compiler rules.

Rejected as substitutes: `SourceEffectId`/family equality, `SourceNodeKey`, `AnnotationMember(view,j)`, operation occurrence provenance, candidate `Contribution.instance`, cached view identity, a return type projection, or `FreshUse` remapping. Each is a bounded native source/inference identity, not the original proof package. No withdrawn Simple-sub bypass is relevant or restored.

Exact owner TODOs:

- **Original Operation / complete-Sigma owner:** supply an accepted derivation for the unchanged original `c` at the actual declaration/reference/substitution, with complete `Sigma/Lambda`, `kappa_c` if it exists, and its independent original license. If selection is new, mark it as a semantic change; this map cannot authorize it.
- **`Sigma.Lambda/A_decl` owner:** supply the actual complete output tuple and its same-`c` dependent field/license/provider/world/scope/future action, including any real typed whole-map and changed-domain evidence. A responder result or same-shaped signature is not that output.
- **Original Contrib/Inc/Cover and ingress/removal consumer owners:** identify the actual consumer judgment whose input is that same licensed field evidence, then provide forward/back behavior and selected/residual lineage on unchanged full inputs. `candidate_check_effect_operand` is not a substitute for those semantic consumers.
- **Native source owner, after the proof inputs above:** identify a real producer for the accepted original fields and correlate them through the actual candidate propagation/cache/FreshUse path to the identified consumer without merging distinct source occurrences or semantic witnesses.

The falsifier for `NO_SAFE_CODE_SLICE` is an accepted proof input fixing original `c`, independently licensing its field, supplying the field action at an actual complete `A_decl` output, and identifying a real producer-to-consumer mapping that preserves all original indices and dependent evidence. If those inputs arrive, return to Luna for a new explicit bounded code lease; this packet grants none.

## Scope, checks and stop receipt

Read-only inspection covered the HIR declaration/lookup/parser owner, Operation action emission, candidate Operation/signature conversion and support/member checking, candidate observations, and FreshUse view/member cache remapping. The r15 candidate's full `q`, `Op-Fixed-Select`, `Op-Fixed-Out`, output-action premises, and source-native claims were compared against these owners. SHA-256 reconciliation is listed above. No tests, builds, compiler edits, runtime, Git operations, new dependencies, or probes were run. No temporary/generated/scratch paths were created.

Requested role/model/effort: `implementer`, Luna/high. Observed effective model/effort: UNKNOWN/UNKNOWN; the current-state snapshot likewise records UNKNOWN. Assignment resource cap: 480 seconds; exact consumed CPU/wall/resource counters are unavailable (UNKNOWN). No descendants. This artifact records a static bounded source audit; it does not represent a live worker launch receipt or independent review. Parent remains OPEN / closure 0.

`NO_SAFE_CODE_SLICE`: current owners cannot generate the fixed-`c` package, independent license, or actual output action that any code slice would need to carry. Writing a tag, adapter or observer would add empty representation without an authentic producer or consumer relation. No provisional instrumentation was created; cleanup owner: none. Writer stopped after freezing the paired artifacts; no descendant or scratch lease remains unresolved.
