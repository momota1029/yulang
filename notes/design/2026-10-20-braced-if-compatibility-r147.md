# Braced `if` bodies for the unchanged countdown sample

Status: **DRAFT — proof-lane source note frozen; pending independent review. No
semantic approval or implementation authority is recorded.**

This decision packet targets the unchanged Web example
`web/playground/examples/yulang2-ordinary-islands.yu`, whose relevant source is:

```yu
my countdown flag = if flag { 8 } else { countdown true }
our countdown_result = countdown false
countdown_result
```

Yulang2 accepts these braced arm bodies. The current Yulang3 `if` parser requires
colon bodies, so this source does not reach inference. The goal is to make this
sample executable while moving toward broad unchanged Yulang2 Web-sample
coverage. This packet does not change colon-form behavior, solver rules,
expected outputs, or runtime semantics, and it does not close any inference,
evaluator, source/native, A/B, or production gate.

## Audited Yulang2 behavior

The oracle parser accepts a brace-owned `BraceGroup` after an `if`/`elsif`
condition and for an `else` body. The group parser supports expression-list
separators and spread syntax. In inference, `lower_expr` first applies
`brace_group_is_record_literal` before selecting record construction or block
lowering (`../yulang2-oracle-capture/crates/infer/src/lowering/expr/chain.rs`).
That predicate and the downstream consumers are distinct:

| Shape | Predicate / consumer path | Evidence boundary |
|---|---|---|
| Empty `{}` | The predicate returns true for no children; record lowering constructs `Pos::Record([])` and `Expr::Record`. | Empty record, not unit. This is historical Y2 behavior, not yet a Y3 rule. |
| Inline record fields such as `{ field: value }` | The predicate accepts inline field expressions; record lowering lowers field values and constructs a record. | Does not behave like a singleton expression list. Field validity can still fail later. |
| One operand-bearing spread `{ ..r }` | The predicate accepts a spread containing an `Expr`; record lowering lowers it, joins its effect, and builds head/tail record-spread form. | Predicate acceptance alone does not prove parser reachability or successful operand typing. |
| Multiple operand-bearing spreads | The predicate can select record lowering; `lower_record_literal` rejects the second spread before lowering that operand. | Routing acceptance is not successful construction. |
| Non-record expression items | The record predicate returns false; `lower_expr_block` uses `block_lowering_items` and block-sequence semantics. | The exact retained/tail result depends on the supported item sequence and must be proved at the constructor/consumer boundary. |
| Non-record mixed spread | The record predicate returns false; `block_lowering_items` keeps `Binding`, `Expr`, and `ForStmt`, excluding `ExprSpread`. | This is a historical omission on this block path. It must not be generalized to record spread or silently copied into Y3. |

Malformed or unexpected children can make the record predicate return false;
this does not establish which shapes the parser can produce or how recovery
behaves. Record routing, record construction, and block lowering therefore
remain separate claims. These facts are pinned in R147 rev2 and must be
reconciled with the proof handoff before this draft is reviewed.

## Current Yulang3 owners

- `crates/yu-syntax/src/expression/if_expr.rs`: the `if`/`elsif` parser stops
  condition scanning at `{` but currently constructs a body only after `:`.
  A bare `else { ... }` takes the inline-body helper; `{` is an inline boundary,
  so the parser emits a missing body and returns the brace to its outer owner.
  Helper dispatch does not mean a brace body was accepted.
- `crates/yu-hir/src/module/local_source.rs`: `Builder::conditional` currently
  accepts `OperatorChain` or `IndentedStatementBlock` for each arm body. A
  dedicated braced-arm CST body needs explicit admission and must preserve
  original source identities, arm order, and the enclosing conditional scope.
- `crates/yu-solver/src/candidate_source.rs`: the existing `LocalSourceForm::If`
  consumer checks every condition against Bool, joins each condition/body
  effect, joins branch values when an `else` exists, and returns Unit when no
  `else` exists. This is an existing implementation path, not a soundness proof.
- `tools/inference-playground/src/runtime/program.rs` and
  `runtime/machine.rs`: the existing ordered `If` runtime consumer is available
  after a correctly formed source carrier reaches it.
- `tools/inference-playground/src/main.rs` / `src/lib.rs`: the CLI selects a
  definition for execution after syntax/HIR/candidate preparation. This packet
  authorizes no execution.
- `apps/yulang-wasm/src/lib.rs`: browser `infer`/`run` delegate to the same
  playground API. `web/playground/src/main.ts` currently selects identity,
  diagnostic, and other fixed examples; it does not import or select the
  ordinary-islands countdown sample. `web/playground/smoke-test.mjs` also does
  not run this sample. Later integration must explicitly add the unchanged
  example and assert `countdown_result -> 8`, while preserving existing smoke
  expectations.

## Decision options

Both options require a dedicated braced-arm body directly owned by `IfArm` or
`ElseArm`; they must not reuse ordinary
`BracedStatementBlockExpression`. Both preserve colon-inline and
colon-indented arms unchanged, source order, condition/body ownership, effects,
arm scope, matching-close ownership, and the existing conditional consumer.
Neither option changes inference rules or A/B claims.

### Option A — narrow countdown support

Accept a braced arm only when it contains exactly one ordinary non-record
expression and no spread. Lower that expression as the existing arm body. Give
empty, record-shaped, spread-bearing, and multi-item forms an explicit
diagnostic. This is the smallest route to the unchanged countdown source, but
it is not broad Yulang2 braced-body compatibility.

### Option B — broader source-compatible bodies with explicit unsupported cases

Support ordinary non-record expression lists under a dedicated arm-list owner,
with source order and explicit left-to-right sequence semantics. The current Y3
`BracedStatementBlockExpression` HIR builder is insufficient: it accepts only
private binding statements before one final expression. This option therefore
requires a dedicated HIR sequence representation and matching inference/runtime
consumers, to be designed and pinned in the later implementation contract.
Preserve record-shaped meaning for empty records, inline fields, and at most one
operand-bearing record spread. Reject malformed lists, duplicate spreads, and
non-record mixed-spread forms explicitly; do not reproduce Y2's silent
`ExprSpread` omission. This covers more source forms and keeps every accepted
item accounted for, while naming the mixed-spread rejection as a deliberate Y3
difference.

Both options must be specified against parser-produced CST shapes and have
focused parser recovery, HIR source-link, inference, runtime, and Web/WASM
coverage before merge. Passing the countdown example alone remains finite
sample evidence, not a language-wide theorem.

**Luna's recommendation:** Option B better serves the stated breadth goal. It
keeps record meaning and useful expression lists, and makes the historical
mixed-spread omission visible as an explicit rejection. Option A remains a
valid smaller adoption if the user wants only the countdown path first.

## After the user decision

Only the exact option and revision approved by the user can authorize a new
implementation contract. That contract must lease the parser/CST, HIR, inference
consumer, runtime/WASM/browser integration, tests, and unchanged sample as one
end-to-end chain, with source proofs and fresh independent review. The new
contract must keep all currently preserved tests and Web smoke expectations.
Until then, the code-writing lane is `NO_SAFE_CODE_SLICE`.
