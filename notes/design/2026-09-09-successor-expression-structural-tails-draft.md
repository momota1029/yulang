# Expression assignment and type-annotation tails

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user's current instruction to make the accepted parser surface
Yulang2-compatible while selecting reasonable successor recovery; exact
compiler/recovery and specification pre-write reviews on 2026-09-09.

Scope: Yulang2-compatible admission of expression assignment and `as Type` in
the successor `OperatorChain`, with a selected successor recovery contract.
This does not authorize canonical AST materialization, HIR association,
operator-table changes, declaration equality changes, Type-attached `impl`, or
any public parse-entry API shape change. It authorizes the public `SyntaxKind`
vocabulary additions `AssignmentTail` and `TypeAnnotationTail`, which are the
reserved flat CST forms for this accepted syntax.

Authority: the user's current instruction fixes accepted input to Yulang2 and
delegates reasonable successor recovery selection. The recovery-authority
amendment requires the selected failing slot, emitted extent, boundary,
continuation and termination to be recorded before construction. The structural
tail topology in the chasa architecture reserves `AssignmentTail` and
`TypeAnnotationTail`; the expression-tail handoff addendum retains the three
handoff exits and flat BP-independent output. This Draft supplies the currently
missing direct-owner detail.

## Oracle evidence

The frozen `yulang2-oracle` tag was peeled to commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1` and exercised in isolated detached
worktrees. Each temporary test was added to `crates/parser/tests/expr_grammar.rs`
and removed before its worktree was removed. The first used
`standard_op_table()` except for a local prefix-`+` registration and ran:

```text
cargo test -p parser --test expr_grammar oracle_assignment_and_as_probe -- --exact --nocapture
```

It accepted `x=-y`, and accepted `x=+y` when `+` was registered as a prefix
operator. `x==y` remained a dynamic infix, not assignment followed by `=`.
The second command was:

```text
cargo test -p parser --test expr_grammar oracle_as_continuation_probe -- --exact --nocapture
```

Its exact observed classification was:

| source | oracle observation | accepted-input conclusion |
| --- | --- | --- |
| `x as int + y` | `TypeAnn` prefix then outer `InvalidToken("+")` | whole source is not recovery-free accepted |
| `x as int; y` | `TypeAnn` prefix then outer `InvalidToken(";")` | whole source is not recovery-free accepted |
| `x as int: y` | `:` is consumed by Type as a polymorphic-variant start; `y` is Type `InvalidToken` | not recovery-free accepted |
| `x as int with: y` | `with` and `:` are consumed by Type application; `y` is Type `InvalidToken` | not recovery-free accepted |
| `x as int as str` | both following words are Type applications | recovery-free accepted Type annotation |
| `x as int y` | `y` is a Type application | recovery-free accepted Type annotation |

These observations agree with
`yulang2-oracle:crates/parser/src/expr/tail.rs:139-170,208-225`,
`expr/scan.rs:238-246` and `scan/mod.rs:152-176`: accepted dynamic operators
are judged before the one-character assignment punctuation fallback. `typ/parse.rs:177-210`
re-enters expression only for Type's `Left(trivia)` result and propagates a
Type Stop; `typ/scan.rs:65-120` makes dynamic `+` a Type Stop. The probes are
accepted-input and stop evidence only; their malformed recovery products are
not successor requirements.

## Owner topology and admission

`expression::operator_chain::tail_normalized` remains the only dispatcher. It
checks active stop, fence boundary, threshold, ML mode and continuation trivia
before either owner commits. A rejected candidate has no output, recovery or
cursor effect.

Two explicit modules carry different responsibilities:

- `expression::tails::assignment` owns exact assignment punctuation, its one
  RHS, its recovery and terminal handoff.
- `expression::tails::type_annotation` owns exact contextual `as`, its
  TypeExpression child and propagation of its Type exit.

They do not share a generic structural-tail module: assignment owns an
Expression/Statement RHS, while annotation owns a Type child. Neither node
owns or wraps a left operand; both append source-ordered children to the open
flat `OperatorChain`.

Both tails are outer-only: `threshold.is_none()` and an enabled non-ML
continuation are required. This preserves effect-free lower-threshold and
ML-argument rejection. `as` is an exact contextual word, never an identifier
ML argument once committed. Leading before a committed `=` or `as` stays a
direct `OperatorChain` child; the tail begins with its literal introducer.

## Assignment

Add `SyntaxKind::AssignmentTail`, `GrammarRole::Assignment(AssignmentRole)`,
and `AssignmentRole::{Rhs, IndentedStatement}`. `Rhs` maps to one
`Expression` expectation; `IndentedStatement` maps to one `Statement`
expectation. Every Missing is zero-width with no unexpected facts, one
committed-rule expectation and primary index zero. Every Error has one
nonempty actual emitted run and one `OtherCharacter` fact.

The expression lexical boundary first keeps an admitted dynamic LED operator.
Only after that decision fails does it acquire exactly one `=` as assignment.
It must not reuse the maximal-run declaration-equals scanner, manufacture an
operator-use node, or split an already acquired malformed Item. This preserves
the accepted prefix-RHS witnesses and the `==` infix control.

After emitting the `=` inside `AssignmentTail`, physical indentation chooses
one RHS:

- a strictly deeper introduced line delegates to the existing indented
  Statement block with `Assignment(IndentedStatement)`;
- otherwise one required inline Expression is parsed at threshold `None`, with
  normal permitted ML mode and inherited stops, fence, line and ambient state.

It is a single RHS, not ColonApplication's comma-owning inline list. On any
successful RHS exit the tail closes and returns that exit to its enclosing
owner without scanning another outer-chain continuation.

Before an inline NUD, a fence/abstract boundary, active stop, explicit line
stop, separator, close, non-NUD bracket opener, non-continuing layout or EOF
publishes one `Assignment(Rhs)` Missing. The abstract boundary anchors at its
inspected coordinate; another protected boundary anchors at remaining-start;
ordinary EOF may first emit its owned leading and anchors at physical EOF. The
whole protected Item and its unowned leading remain pending.

A non-boundary non-NUD emits its initial leading outside Error, then consumes
one maximal lexical run up to an admitted NUD or the same protected boundary.
Internal leading belongs to Error and retry/boundary leading does not. An
admitted retry parses the same single RHS; a boundary after Error returns
unchanged and adds no Missing. Nested accepted Expression recovery keeps its
own existing roles.

## `as Type`

Add `SyntaxKind::TypeAnnotationTail` and `ExpressionRole::TypeAnnotation`.
The committed `as` token is `AsKw`; the tail delegates exactly once to the
existing required full-Type entry with `Expression(TypeAnnotation)` as its
initial Missing role and inherited Type callers/stops/closes/fence/baseline.

This role override is intentionally asymmetric. A missing initial Type has one
`Expression(TypeAnnotation)` Missing with a `TypeExpression` expectation.
Once the Type owner begins a nonempty malformed run, its existing
`Type(Primary)` Error and native unexpected facts remain authoritative; retry
and nested Type recovery retain Type roles. The annotation owner neither
rescans Type source nor relabels those records.

The annotation node owns accepted post-`as` leading, the TypeExpression and
its Type-owned recovery exactly as the required Type entry emits them. Its
initial protected boundary stays unread; terminal Type Error does not add a
second annotation Missing.

## Type exit and continuation

The current successor Type tail scans its successor Item before it decides any
of payload boundary, layout, caller/outer boundary or Type stop. Its
`NormalizedExit` therefore has no safe `Left(Item)` subclass for expression
re-entry: re-scanning would skip that Item, while direct expression dispatch
could reinterpret the observed Type-stopped `+`.

For this gate, `TypeAnnotationTail` closes and propagates the required full
Type exit unchanged. It never invokes `continue_normalized_tail` and does not
add a Type provenance API. This implements every verified Yulang2 accepted
annotation witness without a source replay or acceptance expansion.

The historical architecture's non-terminal annotation reservation remains a
future boundary, not evidence of a currently reachable successor re-entry.
The finite accepted Yulang2 `Left(trivia)` exits are exhausted scanning and
layout/inline/ML stopping (`typ/parse.rs:177-190`). At annotation entry
`ml_arg` is false; Type application consumes its own horizontal continuation.
For exhausted scanning, expression tail has no successor. For each newline
branch, `expr::parse_tail_bp` immediately returns the same layout boundary
instead of admitting a dynamic tail. Thus propagating the successor exit is
accepted-input equivalent for this gate. Malformed-forall `Left` exits are
recovery behavior, not accepted-input evidence, and retain the selected
Type-owned recovery policy. A future addition must first prove a distinct
accepted witness, then define an Item-preserving producer/consumer table for
primary completion, normal Type tail, arrow RHS, application child return and
local delimiter close. It may not infer that information from `TailExit`.

## Product and verification boundary

The already-reserved flat CST nodes are sufficient for syntax construction.
Candidate canonical products remain outside this gate until the separate
materialization Draft is approved: `AssignmentTail { equals, rhs }` and
`TypeAnnotationTail { as_keyword, type_expr }` must not be silently added to
an unapproved AST sum.

Required tests retain all existing source literals and cover dynamic precedence
before one-character assignment (`x=-y`, registered-prefix `x=+y`, `x==y`),
outer-only/ML rejection, single inline and indented assignment RHS, terminal
assignment, flat output under changed binding powers, every protected boundary
before/after Error, fresh/frozen records, UTF-8/CRLF/fence extents, and
declaration-equals controls.

Annotation tests cover full Type families, missing Type versus Type-primary
Error ownership, nested Type recovery, active close/EOF/fence handoff and the
propagated-stop controls: `x as int + y` and `x as int; y` must leave their
stops outside a recovery-free full expression. Any later continuation witness
must first establish Item, leading, origin and line preservation without replay.

Static cost is one bounded tail dispatch and the already-required child parse;
no allocation, replay, retained token list or extra source traversal is
permitted. No benchmark is needed absent material uncertainty.

## Construction gate

This M2 cross-owner construction is complete. Compiler/recovery and
specification pre-write review closed the contract; one implementation pass
added the two named owners, lexical acquisition, public CST vocabulary and
focused tests. Compiler/recovery and regression delta review found and closed
the protected-layout EOF and public-vocabulary record defects.

Focused checks passed: structural tails 8; dynamic operators 11; fixed-tail
recovery 9; `cargo check -p yu-syntax`; scoped `cargo fmt --check`; and
`git diff --check`. Benchmark use was zero. The canonical materialization
decision and Type-attached-Impl promotion remain independent open gates.
