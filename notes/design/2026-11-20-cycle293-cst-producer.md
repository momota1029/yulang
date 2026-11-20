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
