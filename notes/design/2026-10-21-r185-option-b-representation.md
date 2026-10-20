# R185 — Option B representation and consumer design

Status: **research design; not reviewed or authoritative; no implementation
authority**. Source evidence is restricted to the 45 committed blobs pinned in
R185 rev1 at baseline `1ec02864dccccffa9617705b0ddbeaa64176aff5`.

## Outcome and fixed semantics

R184's 38-blob map found no source-HIR sequence or general record literal and
was reviewed with a major finding: it did not name the exact missing owner
`tools/inference-playground/src/runtime/receiving.rs` and obscured an existing
playground formatter/definition-selection owner. This note closes that
reporting gap by separating established definitions from uninspected
consumers. It does not turn the map into a code-ready contract.

R185's proof lane has frozen a scoped local result (note SHA-256
`8e102bfa1badaba2578eaef3cf6e76100d52bdb9b312b22e2368dbc570c47161`): one
completed qualifying negative extrusion of the initial direct-Name chain
cannot selectively lower only one of `t,n,R`; the same copy group carries all
three. This rejects one proposed local attack but leaves universal
`R183-FRONTIER-COVERAGE-1` OPEN. The proof handoff identifies two exact owners
outside R185 rev1's source manifest—`shadow_apply.rs::admit_candidate_fact`
and `candidate_call.rs`—and did not read them. No source-qualified
counterexample follows.

R147 rev2 Option B remains provisional under the user-direction interpretation
recorded in R183. Preserve these cases:

- ordinary non-record brace-body expressions form an ordered sequence,
  evaluate left-to-right, and return the last expression's value;
- `{}` is an empty record;
- inline record fields retain record meaning;
- at most one operand-bearing record spread retains record meaning;
- malformed lists, duplicate spreads, and non-record mixed spreads are
  rejected explicitly; no source item may disappear silently;
- existing no-else `if` continues to produce Unit.

The unchanged Web fixture remains
`web/playground/examples/yulang2-ordinary-islands.yu`, with the required future
observable `countdown_result -> 8`. R185 does not execute it. R167 and R149 stay
separate; this selected-definition path does not close their gates.

## Constructor and consumer map

| Stage | Established owner and evidence | Missing consumer or required design obligation |
|---|---|---|
| If parser/CST | `yu-syntax/src/expression/if_expr.rs::if_arm_normalized` owns conditional arm parsing. It stops the condition at `{`, but the current body branch is entered only for `:`. `else_arm_normalized` routes a non-colon body through inline parsing; `{` is a boundary. `tails/with_body.rs` and `sequence.rs` own existing body/recovery boundaries. `syntax_kind.rs` contains ordinary `BracedStatementBlockExpression`, not a dedicated braced-if owner. | Add a dedicated brace body under `IfArm`/`ElseArm`; preserve matching-close, punctuation, trivia, malformed body, arm successor and source occurrence ownership. `delimited.rs::ProjectionRecordTail` / `ProjectionRecordSpreadItem` belong to projection syntax and cannot be reused as literal-record proof. |
| Parser recovery tests | `tests/if_expr.rs`, `expression_recovery.rs`, `braced_statement_recovery.rs`, `rule_expression_list_recovery.rs`, and `delimited_recovery.rs` cover current owners. The latter record cases are projection-tail recovery. | Add accepted/rejected braced-arm shape matrix, recovery to next arm/expression, unmatched braces, separator failures, duplicate spread and mixed non-record spread cases. Preserve diagnostic ranges and raw source slots. |
| Source HIR and identity | `yu-hir/src/module/local_source.rs::LocalSourceForm` currently has `If` and `Block`; `Builder::conditional` accepts one `OperatorChain` or `IndentedStatementBlock` per body. `Block` carries local bindings plus one final expression. `source_identity.rs` and `shadow_source_core.rs` cover identity/translation owners. | Introduce an occurrence-preserving sequence carrier and record carrier, with stable parent/child identity, ordered children, lexical scope and exact field/spread operand identity. Update formation and identity translation. Reject malformed CST before producing partial HIR. |
| Source value graph | `yu-solver/src/candidate_value_graph.rs` traverses existing If/Block forms and emits If fragment edges for condition/body/else occurrences. `candidate_source.rs` constructs If constraints; `lib.rs` schedules candidate work. | Every new form needs visitor, fragment/semantic edge, owner, schedule, rollback, and resource-accounting coverage. Sequence items must be reachable once in source order; record field/spread expressions need explicit edges. |
| Type representation | `yu-types/src/lib.rs` exposes positive/negative value nodes with scalar, function, union/intersection and quantified/recursive forms; there is no record node. `yu-solver/src/term.rs` is the term arena. | Define record field/row type representation and operations (construction, projection/lookup, spread merge) only after semantics are fixed. A general sequence itself has the final item's type, while each item still contributes effects and must be checked. |
| Constraint construction and solver | `candidate_source.rs` currently handles If: Bool upper bound for conditions; branch values constrain the result when else exists; conditions/bodies join effects; no-else constrains the parent to Unit. `candidate_scheme.rs` owns Capture/FreshUse reconstruction and typed bounds; `candidate_extrusion.rs` and `candidate_intrusion.rs` own movement/merge of actual bounds. `candidate_context.rs`, `candidate_effect.rs`, `candidate_scope.rs`, and `candidate_unit_tests.rs` are pinned downstream owners. | Add constructor-specific source facts without bypassing Simple-sub generation, levels, extrusion, qualifying intrusion or generalization. Preserve all occurrence and effect links through rollback/replay. Record field constraints need a specified row/field relation; sequence result links the final expression but cannot omit earlier item effects or diagnostics. Apply R183's open frontier premise only where a proof dependency actually requires it; do not claim R183 closed. |
| Runtime lowering | `runtime/program.rs::Instruction` and `RuntimeProgram::from_hir` lower current If and Block forms. Instructions include `If` and `Block`; there is no Sequence or Record instruction. | Add an ordered sequence instruction with an explicit successor index/result rule; add record construction and lookup/merge operations consistent with adopted semantics. Exhaustive HIR lowering and code traversal must be updated together. |
| Runtime execution | `runtime/machine.rs::Frame::Condition` chooses an arm in order; `Frame::Local` advances Block bindings; runtime values currently include Unit, scalar, closures, computation and operation, with no record. | A sequence frame must resume after exactly the completed item and retain the environment/view needed for remaining items. Record evaluation order, spread merge and runtime field lookup need explicit rules. No repeated/skipped side effect on suspension, resumption, cancellation or replay. |
| Continuation and received views | `runtime/continuation.rs` stores `TemplateNode::Bind { frame }` as a cloned `Frame` and retains `ExecutionView` in `TemplateNode::View`. **R184's exact omitted owner is `runtime/receiving.rs`**: `Receiving`, `ExecutionView`, `Observation`, schemas and receipts are defined there and imported from `machine.rs` / `continuation.rs`. `runtime/mod.rs` declares it. | Audit the precise receiving/view and restore route before deciding which sequence-frame fields and record values must survive handler capture/resumption. Preserve execution owner, received views and typed raw resumptions. Source shape alone does not prove these lifecycle properties. |
| Value rendering / public entry | `tools/inference-playground/src/lib.rs::execute` selects the named definition and formats Unit, scalar, Closure, Computation and Operation at lines 167–201. This owner is already pinned and is not an unknown dependency. `runtime/mod.rs` owns runtime module/value declarations. `main.rs` is CLI entry. | Add stable record rendering/inspection only after the observable format is chosen. Keep selected definition behavior and existing output formatting. If record rendering belongs in a helper, pin that exact helper in the future code contract. |
| Candidate graph render | `tools/inference-playground/src/render.rs` renders finite candidate graph observations and caps output; it is distinct from user runtime-value output in `lib.rs::execute`. | If sequence/record nodes enter exported graph views, update graph node traversal/formatting or establish that this research-only export intentionally omits them. Do not confuse the two renderers. |
| WASM / Web route | `apps/yulang-wasm/src/lib.rs` delegates `infer`/`run` to the playground API. `web/playground/src/main.ts` owns example selection and calls WASM. `smoke-test.mjs` owns execution and diagnostics expectations. | Import the unchanged ordinary-islands fixture, run `countdown_result`, assert `8`, and keep every existing expectation. Add parser/HIR/inference/effect/runtime-resumption tests before merge. |

## Required representation invariants

1. **Source conservation:** every accepted brace item has exactly one HIR
   occurrence and an identified parent; rejected items have explicit recovery
   or diagnostics. No malformed or non-record spread is silently dropped.
2. **Order:** parser children, HIR sequence children, scheduled constraints,
   effects, and runtime evaluation retain source order. A sequence returns the
   last expression value; earlier effects and errors remain observable.
3. **Scope:** condition, sequence items, record field values and spread operand
   begin in the approved conditional/record scope. No branch-local binding
   semantics may be inferred from ordinary `Block`.
4. **Effects and continuation:** each item/field/spread operand contributes its
   own effect. A suspended early sequence item resumes at the next item once;
   views and owner state required by `receiving.rs` survive continuation.
5. **Record meaning:** the type and runtime representations agree on empty
   record, fields, one spread, access and rendering. No record type or merge
   rule is inferred from projection tails.
6. **No-else compatibility:** the current candidate source and runtime paths
   explicitly return Unit when no else exists. Preserve that behavior unless a
   separate semantic decision says otherwise.

## Unresolved semantic decisions

The pinned R147 Option B packet establishes broad shape intent but does not
provide enough evidence here to define field-name equality, duplicate-field
policy, spread override/merge order, missing-field lookup, or a user-visible
record output format. Do not invent these rules in code. The later exact code
contract must either cite already-approved semantic text for each item or stop
for a narrowly stated decision. This is a semantic dependency, not a missing
runtime owner.

The current 45-source set also does not establish exhaustive repository-wide
consumer closure. In particular, if the design finds any constructor/match or
test owner outside the manifest, request its exact path and immutable pin in a
sequential manifest revision. The concurrent proof lane reports this exact
source-history dependency boundary from its admitted evidence: the actual
Apply admission is at `crates/yu-solver/src/shadow_apply.rs::admit_candidate_fact`,
and it also requests `crates/yu-solver/src/candidate_call.rs` for Formal/Name
registration and native carrier construction. Neither path is in R185 rev1's
45 blobs; their contents have not been read under this packet. The next source
revision must pin both and establish their relevant definitions before proof
work crosses this boundary. Do not infer exhaustiveness from filename presence
or from the successful countdown sample.

## Review gates and falsifiers

This design must receive fresh independent review with the R185 proof result.
Review must verify every accepted/rejected shape from parser occurrence to
runtime value, including receiving/view restoration and existing smoke tests.
The subsequent implementation contract needs a separate CLEAN prospective
review and activation; this artifact grants neither.

Concrete falsifiers include: a source item with no unique HIR identity; a
constraint/effect visitor omitting an item; a branch result not linked to the
last expression; an early effect repeated or skipped after resume; a record
field or spread with no type/runtime consumer; malformed input silently
accepted; changed no-else Unit behavior; or the unchanged fixture not yielding
`countdown_result -> 8` while preserving existing Web expectations.
