# Authoritative: minimal successor rewrite and token transaction amendment

Status: Authoritative

Scope: the isolated `chasa-recover` successor rewrite and the small
`chasa-recover` 0.2 API it directly needs. This amendment replaces the
successor rewrite's local input/state/result topology. It does not change
production dispatch, the legacy chasa parser, or any current public AST
product.

Approved-by: user

Approved-at: 2026-09-03

Reviewed-by: M3 scoped compiler/recovery and specification review; both
initial blocking findings were repaired and re-reviewed on 2026-09-03.

On approval, it supersedes within the isolated successor rewrite only:

- the root-source, `RowanSink`, range-carrying `Item`, and borrowed
  `OperatorChain` requirements in
  `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` and
  `2026-09-02-yu-syntax-expression-tail-handoff-addendum.md`;
- `2026-09-03-yu-syntax-rewrite-direct-functions-no-iscut-amendment.md`'s
  `Recover` root source, `RowanSink`, range, and borrowed result decisions;
- the isolated-rewrite parts of Gate 4 evidence that require a legacy AST or
  source range. Its syntax and ownership controls, including the E5
  `x[a(b)]` correction, remain in force as CST controls.
- `2026-09-03-yu-syntax-g4b-e5-index-call-correction.md`'s
  `OperatorChain` observation only. Its replacement is one CST `IndexItem`
  containing the nested CST `CallTail`, no `IndexSeparator` recovery, and the
  outer `]` owned by the surrounding CST `IndexTail`.
- the Gate 4–6 amendment's isolated-rewrite root-pointer/root-source
  requirement for dynamic-operator successor evidence. A lexical transaction
  or source-only probe reads raw bytes only from its incoming `&str` suffix
  and retains no root source, cursor, range, or source-relative position. Its
  existing immediate scalar site/fixity, leading-trivia, layout-baseline, and
  active-stop inputs stay explicit owner arguments; they do not justify a
  context object or cache.

## 1. Minimal parser shape

The successor parser is a direct recursive-descent parser. Repeated input
spelling is hidden behind a rewrite-local `type` alias for
`In<&str, &mut Recover<'_>, &mut GreenNodeBuilder<'static>>`; the alias keeps
the reborrow lifetime distinct from the source, operator-table, and builder
lifetimes. Grammar procedures receive that alias plus only their immediate
owner arguments. They do not receive a context object, cursor object, output
wrapper, parser-local frame, token vector, scanner cache, or result stack.

Those grammar procedures are called directly, for example
`expr(i.rb(), level)`. They are not routed through a `ParserOnce` wrapper and
`check` does not need to expose `S`. A direct procedure returns `None` only at
its effect-free entry: every multi-character uncertainty is first resolved by
a `token` parser, and an owner emits to the builder only after accepting its
branch. This is the structural direct-parser contract, not a new global state
or a runtime attempt to roll back Rowan output.

`I = &str` remains the sole source cursor. `with_str` is the way a procedure
captures text it consumed. There is no root source field, source-origin
cursor, source-relative offset helper, or range lookup in the successor
rewrite.

For the first successor slice, `R` is `Recover` containing only the immutable
`OperatorTable` reference, and `Recoverable::Mark = ()`. It never contains
source text, a root slice, a range, a sink, a context, recovery publication,
or a parser-wide cache. A later mutable rollback fact requires its own
approved owner and rollback contract; it cannot be added as a general
`Recover` escape hatch.

`S` is the direct `GreenNodeBuilder<'static>`, not `RowanSink`. A committed
owner calls the builder's `start_node`, `token`, and `finish_node` methods
itself. The builder receives the text captured at the point of consumption;
it has no source/root field and no coverage/range side channel.

No successor parser result, `Item`, `End`, token, trivia record, recovery
record, or internal expression product borrows the source. The isolated parse
result is the owned green tree plus, when recovery facts exist, owned recovery
facts. It is not an `OperatorChain<'source>` or any other borrowed AST.

An unaccepted logical item owns its leading trivia and lexical text. Handoff
therefore moves the same item without a source rewind or a rescan. `Range` is
not used as a substitute for that ownership anywhere in the successor
rewrite.

## 2. The lexical transaction exception

An ordinary function used through `ParserOnce` retains the normal rule:
`None` means it did not consume input. The blanket function implementation
checks that rule by cheap input-index identity and rolls `R` back, but never
rewinds input after a violation. Direct recursive owners obey the same
nonconsumption result by their effect-free-entry structure in §1, rather than
by invoking that wrapper.

Lexical recognition is the one explicit exception. `token(f)` is a parser
whose `f` is a raw unit-state procedure
`FnOnce(In<I, R, ()>) -> Option<O>`, executed directly rather than through the
ordinary function `ParserOnce` boundary. It takes an input and `R` checkpoint
before calling `f`. On `None`, it restores both; on `Some`, it commits. It has
no `S`, no Rowan effect, no token cache, and no broader grammar rollback.

Mechanically, its callback bound is
`F: for<'short> FnOnce(In<'short, I, R, ()>) -> Option<O>`, so every call
receives a short unit-state reborrow.

The free parser form has `ParserOnce<I, R, ()>` and is for tuple, choice, and
`maybe` composition. `In::check` remains unit-state-only. `In::token(f)` is
the separate outer-state convenience spelling: it constructs the same private
short `S = ()` reborrow as `check`, then runs `token(f)`. Thus `f` cannot
observe, checkpoint, or mutate Rowan state. A token procedure is a small
lexical recognizer, not an excuse to make an expression, a delimiter owner, or
an arbitrary recursive parser speculative.

`maybe(p)` is the ordinary optional parser over a unit-state `ParserOnce`.
Its `run_once` result is `Some(Some(value))` when `p` succeeds and
`Some(None)` when `p` non-matches. `In::maybe(p)` likewise makes a private
short unit-state reborrow, with the same `Option<Option<O>>` shape. `maybe`
adds no checkpoint of its own: the inner parser owns its non-match contract,
and `token` owns the only consume-then-non-match rollback exception.

The resulting two outcomes stay visible:

| procedure | `None` after consuming input |
| --- | --- |
| ordinary function used as `ParserOnce` | contract violation; fail fast after `R` rollback |
| direct recursive owner | forbidden by its effect-free-entry structure |
| `token` lexical procedure | input and `R` roll back; ordinary lexical non-match |
| `maybe(p)` | asks `p`; produces an optional successful value |

`choice`, tuples, and the future `fold` helper may compose these parsers, but
they do not gain an additional rewind rule. Pratt `Err(Item)` remains a
separate owner handoff and is not a parser non-match.

## 3. Immediate rewrite consequences

The existing uncommitted rewrite shell is an intermediate topology, not a base
to preserve. Its `RowanSink`, root/range helpers, source-borrowed
`OperatorChain`, and range-backed item/recovery records are deleted or
replaced when the approved successor foundation is implemented. No legacy
AST/range assertion is mechanically retained merely because it currently
passes.

The first implementation slice is deliberately narrow:

1. add and test `token`/`maybe` in `chasa-recover`;
2. replace the rewrite's source/range/sink/result scaffolding with the
   alias, source-free `Recover`, direct builder, and owned lexical item;
3. rebuild one direct CST-only expression closure with the existing
   `expr`/`tail` Item-or-End handoff, including `x[a(b)]` once the index owner
   is reached.

Gate 4 and G4b remain open: slices 1–2 close no coverage-ledger cell. Slice 3
is only a new isolated CST foundation until its assigned controls are reviewed.
When it reaches E5, it observes exactly one `IndexTail` with one `IndexItem`,
an ordinary nested `CallTail`, no `IndexSeparator` recovery, and direct outer
`]` ownership. No Gate 4b completion, production promotion, AST parity, or
Yumark streaming claim follows from any earlier slice. The existing G4a commit
remains history, but its old certification is not evidence for this new
CST-only topology. A later authoritative gate must decide how an owned
successor CST is consumed by any public AST or production interface.

## 4. Focused evidence

The first slice proves only the new local contract:

- `token` rolls back consumed `&str` input and a mutable test `Recoverable`
  state on a lexical non-match, including UTF-8 input, and commits both on
  success;
- ordinary functions used as `ParserOnce` still fail fast for
  consume-then-`None`;
- `maybe(token(...))` distinguishes matched and absent lexical values without
  changing the cursor or `R` on absence, producing respectively
  `Some(Some(value))` and `Some(None)`;
- a `token` called from an `S`-carrying rewrite handle exposes no builder to
  its raw procedure and cannot create a speculative Rowan effect;
- an isolated direct expression result is an owned `GreenNode`, without a
  source lifetime, `RowanSink`, source root, range, or `OperatorChain`;
- an unaccepted Item retains owned leading trivia and text through one tail
  handoff; accepted text is emitted directly to the builder.

Broader legacy tests are not rewritten to satisfy this evidence. Tests for the
new closure are added only as the closure exists; recovery diagnostics,
production integration, and all remaining syntax owners require later gates.

## Implementation status

The `chasa-recover` `token`/`maybe` slice completed on 2026-09-03. It adds the
unit-state `Token` and `Maybe` parser forms, the two narrow outer-state
conveniences, and their focused contract tests. The M3 compiler/recovery
implementation review found an over-broad outer-state `check`; the repair
restored unit-state-only `check` and received a clean scoped closure review.
`cargo test -p chasa-recover` passed 19 tests after that repair.

This completion implements step 1 only. It neither changes the rewrite shell
nor closes a Gate 4/G4b cell.
