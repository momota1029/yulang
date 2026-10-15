# Unary lambda parser for the Callback Hygiene source

Status: Reviewed; user approval pending; no implementation authority
Date: 2026-10-15
Scope: complete unary identifier lambda admission, lossless CST and body recovery in yu-syntax
Baseline: `13a8e36eb595e97b5667230c7463fdb09aed67b8`
Drafted-by: primary from bounded architect callback_lambda_gate
Reviewed-by: independent compiler_referee lambda_semantic_review and spec_auditor lambda_spec_review; no remaining blocking/major findings
Approved-by: pending
Supersedes: none until approval; the proposed narrow changes are listed in section 1

## 1. Concrete blocker and retained authority

The unchanged [Callback Hygiene input](../../tools/inference-playground/oracle/callback-hygiene.yu)
contains `g \i -> if i == 0: return i`. The current production expression
parser does not recognize an inline lambda. The tests in
`crates/yu-syntax/src/tests/tails.rs` explicitly characterize that gap; their
Error-token expectations do not define the intended language behavior.

The [syntax architecture](2026-08-20-yu-syntax-chasa-architecture.md) classifies
lambda as a structural primary but defers its grammar. The
[vertical implementation amendment](2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md)
permits a concrete source blocker to trigger a scoped construction decision.
The [historical callback draft](2026-10-04-production-callback-endpoint-generation-draft.md)
section 2 describes this spelling and complete-header arbitration, but remains
Draft. This proposal selects only a parser realization. It adopts none of that
document's expected-callback, endpoint-generation or F5 construction.

The existing one lossless Rowan CST, current-Item lexical transaction,
source-order/trivia ownership, CST-derived diagnostics and caller fence/close
handoff contracts remain binding. Dynamic operator association remains a
separate phase.

On approval this addendum narrowly supersedes the architecture's LED
operator-first arbitration for a complete lambda header, and the enclosing ML
argument's nonempty-trivia stop while parsing the lambda body (architecture
sections around lines 9920–9928 and 9976–9984 at this baseline). Ordinary
operator arbitration and ML-argument boundaries elsewhere remain binding.
These are the explicit precedence/body choices in sections 2–3, not broader
changes to operator association or layout.

## 2. Proposed complete-header admission

```text
LambdaExpression := Backslash Gap Identifier Gap ExactArrow Expression
Backslash        := "\\"
ExactArrow       := existing exact maximal "->" token
```

`Gap` accepts empty or existing inline trivia without a logical layout newline.
Use the existing classification for comments and opaque block-comment newlines;
the predicate must not cross a fence. The body uses the ordinary enclosing
expression layout and stop rules.

At an expression-primary admission point, recognize the entire header before
dynamic operator selection. Recognition is source-only evidence: no Rowan
output, diagnostics, retained source copy, successor Item or persistent parser
state is created by this predicate. Actual consumption uses the ordinary
lexical transaction for each header Item exactly once.

The admission must be available in both NUD expression entry and the LED
scan that admits an ordinary ML argument. This is required for the actual
unparenthesized `g \i -> ...` source. A complete header takes precedence over
a registered backslash operator, independent of its binding power.

A nonmatching prefix preserves existing selection/recovery. In particular
`\`, `\x`, `\x -`, `\ ->`, and `\x y ->` introduce no lambda node or
speculative lambda diagnostic. Reuse the existing exact-arrow scanner's
maximal boundary: `\x ->> x` must not consume `->` from `->>`.

The binder uses the existing raw maximal identifier grammar, including Unicode,
`_`, and a terminal `?` or `!`, before dynamic word-operator or contextual
expression-keyword selection. This fixes lexical ownership only. Binding,
wildcard meaning, name resolution and capture belong to later HIR work.

## 3. CST ownership and body

Add a `LambdaExpression` CST kind and an internal Backslash token kind; reuse
the existing public Backslash and Arrow syntax tokens. The lambda owns:

```text
LambdaExpression
  Backslash
  header trivia / Identifier
  header trivia / Arrow
  OperatorChain (body, including its ordinary recovery structure)
```

Emit introducer-leading trivia before opening the lambda node. Subsequent
trivia ownership follows the existing current-Item contract. Rowan determines
byte ranges; there is no second range ledger, AST or reconstructed Error CST.
The existing `MlArgument` and `CallTail` nesting wraps this primary normally.

Parse the body as one full ordinary expression, preserving the caller's stops,
layout baseline and fences. It does not inherit an outer operator association
threshold. Thus `f \x -> g x` places `g x` inside the lambda body; a nested
lambda is an ordinary body primary.

After a complete header commits, absent body input uses the existing mandatory
operand `Missing` construction in the body; invalid input uses existing Error
recovery and forward progress. Preserve the recognized binder. Return an
unconsumed comma, enclosing close, separating newline or fence to its existing
owner. Do not roll back an emitted header or consume a boundary to manufacture
a body. CST-derived generic diagnostics are sufficient where the existing
schema permits them; this gate does not require an exhaustive malformed-input
catalog or new diagnostic wording.

## 4. Construction obligations and implementation gate

The implementation must establish:

1. Failed header admission has no parse effects and preserves the existing
   nonmatching operator/recovery route.
2. A matching header consumes each source Item once, preserves every source
   byte and owns the introducer/binder/arrow in one lambda node.
3. The body obeys the enclosing expression boundary and recovery progress;
   a recognized header survives missing/invalid body recovery.
4. Production parsing and ML-argument admission use the same complete-header
   rule, including exact arrow and identifier boundaries.

The existing lexical transaction and mandatory-operand mechanisms should
provide these invariants. Their exact source correspondence must be checked
while implementing; this document is a construction contract, not a completed
parser proof. Stop the affected slice if the existing handoff API cannot retain
these boundaries or if recognition requires recursive speculation. Resolve
that precise contradiction through design review.

Expected implementation owners: expression dispatch/NUD and ML-argument
admission, a dedicated lambda parser, lexical header token selection,
syntax-kind/recovery token mapping, and focused syntax tests. Adjust exact file
placement to existing ownership; do not introduce another syntax product.
Header lookahead examines only its prefix and trivia; account for the extra
lexical pass and prove progress. No timing experiment is selected.

Use M3 with one compiler referee and one specification auditor. Before changing
the historical research expectations, the auditor must confirm that they
record the old gap rather than an accepted rejection contract. Focused checks
cover production parsing of the actual lambda-containing expression,
parenthesized/call arguments, operator collisions, exact arrow, maximal
Unicode/suffixed/contextual binders, incomplete headers, nested/body
application, missing/invalid body, caller boundaries, lossless bytes and ranges.
Run one suitable package check after the coherent implementation slice. No
workspace-wide test or performance sweep is selected.

This parser gate is complete only after focused verification and independent
review leave no accepted blocking/major finding. Full original-file inference
is not its acceptance criterion: imports, loop syntax, library dependencies,
inline-lambda HIR, effect hygiene and execution have separate owners.

## 5. Requested decision

Approve sections 2–4 for the first parser implementation: reserve only the
complete `\ Identifier ->` header ahead of operator lookup, use the stated
inline-trivia/identifier rules and dedicated CST, and inherit ordinary body
boundaries/recovery. This authorizes the parser slice and its necessary tests.
Additional lambda parameter forms and HIR/runtime integration are subsequent
gates; this implementation envelope is not a language-wide rejection rule.

Alternatively defer this parser construction and continue the native inference
and receiving-boundary work. The unchanged Callback Hygiene input then retains
this known parser blocker. Approval of this document would not certify any
inference, hygiene, soundness or runtime theorem.

## 6. Independent review

M3 design review used two independent read-only roles on the frozen proposal.
The compiler referee found no findings. The specification auditor found one
minor missing supersession locator; section 1 now names the two affected
architecture clauses. Neither review supplies user approval or implementation
evidence. Primary inspection closes this documentary repair.

The specification auditor confirms that the two historical Error/prefix tests
in `tails.rs` characterize the old parser gap. After approval, replacing their
expectations with assertions for the selected production construction is
permitted; record the causal contract change and preserve nonmatching controls.

Source inspection identifies three concrete implementation checks: explicitly
restore `MlMode::All` for the body, wrap mandatory-operand recovery with the
enclosing baseline/newline boundary, and use logical trivia classification
rather than raw newline bytes inside opaque block comments. These implement
the existing proposed contract; they are not additional semantic choices.
No parser code, test, build or performance experiment changed in this review.
