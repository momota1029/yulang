# R184 — Option B source-owner map

Status: `NO_SAFE_CODE_CONTRACT`. This is a read-only map of the committed
baseline `1ec02864dccccffa9617705b0ddbeaa64176aff5`. The Option B behavior is
provisional; this note does not close R183 or authorize code, tests, builds,
execution, or production use.

## Decision summary

The 38 pinned blobs identify the current if parser, source-HIR formation,
constraint constructor, experimental runtime, and Web route. They do not define
a complete representation for Option B. In particular, the expression HIR
has no ordered value-sequence or record form, and the runtime has no record
value or sequence instruction. Existing record-tail syntax is specifically
projection syntax. The contract cannot safely prescribe edits or claim an
end-to-end source-to-runtime path until the sequence/record construction and
all affected consumers are specified together.

The unchanged target fixture is
`web/playground/examples/yulang2-ordinary-islands.yu`; its required eventual
observable is `countdown_result -> 8`. This mapping did not execute it. The
fixture itself is in the manifest, while the source that defines its intended
Yulang2 semantics is not. Consequently, the exact source-level record lookup,
record spread merge, and selected-definition route still need a pinned
semantic source or explicit Option B decision evidence in the implementation
contract.

## Shape and owner matrix

| Option B shape | Current constructor / representation | Consumers and concrete gap | Regression owner and falsifier |
|---|---|---|---|
| `if c: e` / `elsif c: e` / `else: e` | `yu-syntax/src/expression/if_expr.rs` constructs `IfArm` / `ElseArm`; body path is colon or inline. `yu-hir/src/module/local_source.rs::Builder::conditional` accepts one `OperatorChain` or `IndentedStatementBlock` child per arm and creates `LocalSourceForm::If { arms, else_branch }`. | `candidate_source` turns each condition into Bool upper-bound and links each arm body value to the if result only when else exists; effects from condition/body feed the parent. `RuntimeProgram::from_hir` creates `Instruction::If`; machine `Frame::Condition` tests in order, selects one body, and yields Unit without else. This is a single-body branch path, not an expression-list path. | `yu-syntax/src/tests/if_expr.rs`, HIR source traversal tests in `candidate_value_graph.rs`, candidate conditional test in `candidate_source.rs`, runtime tests in `program.rs` / `machine.rs`. Falsifier: a branch body with two source expressions cannot be represented while retaining both occurrence identities and returning the final value. |
| Braced if/else body, e.g. `if c { a; b }` | `if_expr.rs` recognizes colon/body ownership; `tails/with_body.rs` treats `{` as a boundary when the current caller disallows braced body. `syntax_kind.rs` has `BracedStatementBlockExpression`, but that is the ordinary block construct. | `Builder::conditional` rejects `BracedStatementBlockExpression`; `else_arm_normalized` routes non-colon body through inline-body parsing. Ordinary block HIR can carry bindings and one final expression, but is not a branch sequence and cannot silently stand in for the selected list semantics. | `if_expr.rs`, `expression_recovery.rs`, `braced_statement_recovery.rs`, `shadow_source_core.rs`. Falsifier: accepted braced syntax has no dedicated arm topology or recovery facts and cannot prove that malformed braces preserve pending tokens and sibling arms. |
| Ordinary multi-expression branch list, evaluated left-to-right with final result | `sequence.rs` and `rule/expression_list.rs` describe parser sequence ownership and recovery, not executable branch-value HIR. `LocalSourceForm` has no `Sequence`; `Block` stores bindings plus one final expression. | `candidate_source` has no sequence constructor/ordered fold; `candidate_value_graph` and source scheduling traverse current `If` and `Block` children only. Runtime `Instruction` / `Frame` have no sequence case. A correct frame must retain next index and environment across effects, suspension, resume, and replay; `continuation.rs` stores ordinary frames in saved continuation templates. | `rule_expression_list_recovery.rs`, `braced_statement_recovery.rs`, `shadow_source_core.rs`, `candidate_source.rs`, `candidate_value_graph.rs`, `runtime/machine.rs`, `runtime/continuation.rs`. Falsifier: an effect in an early list item resumes at the wrong item, duplicates/skips an occurrence, or returns a non-final value. |
| Empty record `{}` | No general record literal CST/HIR constructor is present in the pinned `syntax_kind.rs` / `LocalSourceForm`. `DelimitedOwner::ProjectionRecord` and `ProjectionRecordTail` parse projection-tail structure only. | No record type/value constructor, empty-record value, record constraint, runtime instruction, runtime record value, or output formatting exists in the pinned expression/runtime representations. | `delimited_recovery.rs` currently checks projection-record recovery. Falsifier: `{}` is accepted as an expression but has no unique empty-record value with a stable observable result. |
| Inline record fields | No general record literal expression syntax or source-HIR form is defined in the manifest. Projection record parsing is not a literal owner. | No field-name/value occurrence mapping, field type constraints, field lookup, duplicate-field policy, runtime field storage, or output representation is found in the mapped consumers. | Add focused parser, HIR identity/order, inference, runtime, and Web checks under the future code contract. Falsifier: field values are reordered/dropped, duplicate fields pass contrary to the selected rule, or lookup differs from the fixture’s intended semantics. |
| At most one operand-bearing record spread | `delimited.rs` has `ProjectionRecordSpreadItem`, but in projection-tail context. It is not evidence of a record value spread. | No literal-spread constructor or consumer exists in the source value graph, constraint builder, runtime, or formatter. The operand’s type/value/effects and field override/merge semantics therefore have no owner. | `delimited_recovery.rs` spread tests concern projection tails only. Falsifier: a spread operand is accepted without preserving its evaluation/effect or without a defined merge result. |
| Malformed record lists, duplicate spreads, mixed non-record spreads | Existing delimited recovery records raw slots and structural errors for delimited owners; this does not establish literal-record policy. | No literal parser rejection contract or inference-time record/non-record validation is defined. | Pin both parser recovery and type rejection owners. Falsifier: malformed input is silently ignored, a second spread is accepted, or a non-record operand is treated as a record. |
| No-else if | Existing supported behavior. | `candidate_source` explicitly gives the parent Unit and discards body values while still checking/evaluating the body and joining effects. Runtime returns Unit after selected body. Option B must preserve this behavior unless R147’s exact reviewed semantics explicitly changes it. | Existing if parser / source / runtime tests. Falsifier: a no-else branch becomes a value-producing conditional without an explicit semantic decision. |

## Consumer route and boundary

1. **Parser and recovery.** `if_expr.rs`, `tails/colon.rs`, and
   `tails/with_body.rs` own conditional/body formation. `sequence.rs` and
   `rule/expression_list.rs` own expression-list parsing/recovery. The
   braced-statement parser owns general `{ ... }` blocks. The current source
   does not connect these into a braced if-arm list. `delimited.rs` owns
   projection tuple/record tails and spread recovery, not a record literal.
2. **Source HIR and identity.** `local_source.rs` creates stable expression
   indices, occurrence identities, lexical scopes, and child scheduling.
   `LocalSourceForm` covers `If` and `Block`, but not a value sequence or
   record. `source_identity.rs` is the source-identity authority; every new
   list item, field, and spread operand needs a unique source occurrence and
   an explicit parent/child path. The exact future identity constructor must
   be pinned in the implementation contract.
3. **Constraints and consumers.** `candidate_source.rs` constructs direct
   source constraints and effect links for current forms. `candidate_value_graph.rs`
   builds source-value reachability, and `lib.rs` schedules candidate source
   work. `candidate_context.rs`, `candidate_effect.rs`, and `candidate_scope.rs`
   own context/effect/scope state and downstream relation processing, but the
   pinned forms do not provide sequence or record constructors for them to
   consume. New nodes must be threaded through every visitor, sizing/accounting,
   rollback, and scheduling path, not just the central `If` match.
4. **Evaluation and effects.** `runtime/program.rs` lowers current HIR forms;
   `runtime/machine.rs` evaluates `If` and `Block`; `runtime/continuation.rs`
   preserves saved frames during effect continuation/replay. A sequence needs
   an explicit left-to-right successor state and a specified result rule.
   Record fields/spread need specified evaluation order, merge behavior, and
   runtime lookup/output. `RuntimeValueKind` presently has no Record.
5. **Public route.** `tools/inference-playground/src/lib.rs::execute` prepares
   HIR, constructs the experimental runtime program, selects a named
   definition, and starts its source schedule. `apps/yulang-wasm/src/lib.rs`
   exposes the playground infer/run route. `web/playground/src/main.ts` owns
   sample selection and invokes WASM; `web/playground/smoke-test.mjs` owns
   current execution/diagnostic regression examples. The target fixture is
   not currently imported or included in smoke expectations, so implementation
   must add an unchanged-fixture assertion for `countdown_result -> 8` and
   keep all existing expectations.

## Proof and test obligations for a later contract

- Preserve the R147 shape rules and reject every malformed/duplicate/mixed
  spread explicitly; no accepted source item may disappear.
- Prove source occurrence preservation and left-to-right order from CST through
  HIR, constraints, effects, and runtime, including nested blocks and ifs.
- Prove sequence continuation state is captured/restored exactly through
  effect handling, resumption, and replay.
- Define and test empty-record, inline-field, spread merge, field access, and
  output semantics. Include duplicate field behavior if source grammar permits
  it; do not infer it from projection syntax.
- Keep the existing no-else Unit behavior and all existing inference/runtime/
  Web expectations unless the reviewed semantic decision says otherwise.
- Add parser recovery tests for accepted arm slots, missing braces, separators,
  duplicate spreads, and recovery to the next arm/expression; add HIR identity
  and order tests, inference/effect checks, runtime continuation checks, and
  an unchanged Web fixture assertion.
- Independently verify each future implementation source owner against the
  source manifest before code activation. The current map is not that review.

## Exact missing evidence and next manifest request

`NO_SAFE_CODE_CONTRACT` is required because this manifest shows absent
representations but does not close the owner set for their introduction. A
sequential manifest revision should pin:

1. the grammar/specification or reviewed decision that defines record literal
   syntax, field/spread semantics, record access, malformed-list policy, and
   the unchanged fixture's intended language behavior;
2. the CST-to-HIR source identity and expression formation owners, including
   all `LocalSourceForm` construction/matching sites and source-identity
   translation/recovery consumers;
3. all solver visitors and consumers of source expressions, including
   candidate value graph traversal, context/scope/effect scheduling, relation
   collection, resource accounting, rollback, and any exhaustive form matches;
4. runtime value formatting/inspection and all instruction/frame dispatch,
   continuation capture/replay, selected-definition execution, plus public
   CLI/WASM/Web entry points;
5. focused parser/HIR/solver/runtime/Web test modules and fixture assets.

The current 38 blobs include likely central owners, but a text search or one
central match does not prove exhaustiveness. The precise new paths must be
enumerated and SHA-pinned before further source inspection. Keep dirty worktree
bytes and external Yulang2 worktrees excluded.

## Falsifier

The conclusion changes only if the pinned source set can demonstrate a complete
accepted-shape path from each source token/occurrence through recovery, HIR,
constraint/effect consumers, runtime instruction/value, continuation handling,
public Web run route, and focused tests, with no missing exhaustive consumer.
In particular, a single successful parse or runtime sample is insufficient if
an effectful early sequence item can be skipped/duplicated on resume or a
record literal has no defined type/value consumer.
