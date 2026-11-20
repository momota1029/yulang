# Cycle 293: direct CST shape to an unresolved role

Start from the documented Rowan role topology and the actual Rust emissions,
not from preclassified binder/member DTOs. Verify a narrow topology: plain
or explicitly visible role, one TypeExpression head, ordered simple
TypeApplyArgument nodes, and an indented role body under an actual colon.
Every direct statement must have exactly one selected child; recognize
ordinary TypeDeclaration and a clean ordinary BindingStatement only.
A nested declaration must never be mistaken for a direct role member;
unrecognized topologies fail the adapter, not the language.

Keep raw mixed child indices before ignoring trivia, so path handles are
anchored to a single supplied parse/tree and lost positions are detectable.
Separate a raw exported tree from the Rust SourceNode that could emit it.
The existing public parser exposes CST but the current environment has no
Rust toolchain. No Rust execution, production export or name resolution is
claimed. Scope and parse identity are independently supplied.

## Cross-check against the Rust boundary

- `role_decl.rs` enters the ordinary type-expression code for the head and
  delegates the strictly deeper colon body to the normal statement owner.
  `statement.rs` emits IndentedStatementBlock, and
  `type_expr/mod.rs` emits actual Identifier/SigilIdentifier tokens and
  explicit TypeApplyArgument nodes. No binder list is already emitted for
  the role head.
- `type_decl.rs` distinguishes ordinary bare form from actual Equals plus
  TypeExpression. The existing Rust missing-RHS test confirms a zero-length
  TypeExpression wrapper with a nested Missing node, not an absent RHS.
  This is outside the adapter; the test source was read, not run.
- Mixed element locations are based on `children_with_tokens()`, not
  node-only `SourceNode::children()`, not a filtered trivia ordinal and not
  Rust's distinct `direct_root_ordinal()`. The actual diagnostic walker
  holds all children with tokens and pushes its mixed index; the typed
  occurrence path is exposed by `SyntaxDiagnosticIdentity::occurrence_path()`.
  `StructuralRecovery::path()` gives a *kind* path, not that index sequence.
  Diagnostic paths (including error-group slots) are not assumed to be
  the same thing as declaration occurrence addresses.
- An eventual Rust transfer must use the complete mixed children, preserve
  token/node distinctions and order, specifically map Missing/Invalid/Error
  and resource-limited NestingTooDeep (never bury in generic clean Other),
  and only map audited actual trivia kinds to trivia. Unknown kinds in a
  position claimed as role syntax are not silently erased. Generic Other
  beneath an accepted binding is allowed only for non-recovery kinds; no
  method semantics are inspected. This is a transfer contract, not an
  assertion that Rust already emits the Lean mirror.
- The CST-only stage cannot decide whether a simple RHS identifier denotes
  a constructor/type alias or assign a role or associated-name ID. The
  closed Index consumer supplies the old independent fixture environment;
  the unresolved extract function takes no environment.

An occurrence byte range can be replayed from the complete token widths and
mixed ordinal path. This is a projection on the supplied mirror (UTF-8 bytes).
It cannot certify Rust ranges if the upstream transport loses tokens.

## Wire boundary (portable, no Rust parser replacement)

The portable reader may take the exact current Rust SyntaxKind variant names
and an explicit node/token discriminator. It rejects labels outside the
audited finite enum; Node/Token structure and every payload and slot are
preserved. Actual Newline/Whitespace and comments are recognized as trivia
only when token-shaped. Unknown lexical tokens and NestingTooDeep are marked
conservatively as recovery rather than passed as opaque method content.
Nothing here resolves user names, parses source text, or supplies a Rust
serializer already connected to ParsedFile.

For a bounded portable wire reader, the proposed JSON data schema is exact:
[`"token"`, Rust tag, token text] or [`"node"`, Rust tag, ordered child array].
The depth limit is a transport resource bound, not part of Yulang grammar.
Snapshot brand and selected path are explicit outside this data. A parser
serializer can stream the ordered tags and raw token spellings; no numeric
role ID belongs in the structure.

## What the portable entry verifies

From the repository root, with the prior Lean dependency cache and new
modules built, use `python3 notes/verification/cycle293/test-json-cli.py`
or from `lean/`:

```sh
lake env lean --trust=0 --run ../notes/verification/cycle293/run-unresolved-cst.lean \
  ../notes/verification/cycle293/documented-cst.json 0
```

The argument 0 selects the role through the root's original mixed child
positions. The fixture is reconstructed from the documented Rust CST, not
captured from a Rust parser run. This execution verifies the actual Lean JSON
transport and projector. It does not validate the Rust exporter that would
supply these inputs. In particular two accepted tagged input trees can agree
on every byte of spelling but differ on whether a child is a TypeDeclaration.
This is a synthetic counterexample to using byte equality as an authenticity
certificate, not a parser failure. Preserve distinct snapshot brands, and keep
the original wire if original unclassified labels are needed.

## Exact current Rust golden: avoid a misleading shallow model

The checked-in `role_method_signature_where_keeps_its_pre_wp17_recovery_cst`
in `crates/yu-syntax/src/tests/declaration/act_decl/operation_where.rs`
records the exact Rowan output from `syntax_guide_check --tree`. In that
fixture, `TypeApplyArgument` wraps a `TypeExpression` node before the
SigilIdentifier token. The earlier documentation describes the role argument
without showing this inner node; treating it as a direct token is insufficient
for real Rust topology. The final CLI therefore uses the strict wrapped
head, while the earlier shallow proof modules remain separately named
controls. The wrapped extractor does not rewrite the original tree or the
ordinal addresses below it.

The provided `rowan-debug-to-wire.py` reads the bounded format of this exact
recorded golden, reconstructs each token from the specified UTF-8 byte
range, checks token/debug text and node coverage, and emits the tagged JSON.
The final CLI replays it as unresolved role `a`, binder `'x`, one
non-type binding at `[0,4,2,0]`. That role is at `[0]`. There is recorded
recovery after the role at the root, so successful *selected-role* extraction
does not imply a clean source file. The golden contains no associated type;
the required and default cases are independently reconstructed controls using
the documented role plus the confirmed TypeExpression wrapper. No fresh
Rust invocation or stable general-purpose debug API is asserted.

With Cargo in a future workspace: run the exact existing Rust test first,
capture one additionally selected source role with a required/default member,
and compare the trusted owner walk with the CLI output. Keep direct
`NodeOrToken` tags and order; do not implement the production handoff against
a formatted Debug string.
