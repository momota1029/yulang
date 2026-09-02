# Authoritative: Yumark Gate 3b canonical recovery episodes

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-02

Scope: the recovery-observation infrastructure needed to make an embedded
Yulang payload retain exact canonical recovery facts in its isolated Yumark
AST/direct adapters. This is a Gate 3b infrastructure slice before Gate 3 can
claim malformed canonical-payload closure.

User decision: implement shared, owner-local canonical recovery episodes across
the transitive embedded-payload closure. Preserve ordinary AST behavior; do not
limit or defer compound canonical payload recovery.

Supersedes: only the false assumption in the Gate 3 allocation that existing
canonical AST recovery ownership is already shared with direct parsing. It
supplements, and otherwise leaves intact,
`2026-09-01-yumark-gate3-embedded-yulang-allocation-amendment.md`.

## 1. Contradiction

The Gate 3 bridge must simultaneously preserve full canonical payload grammar,
malformed-payload AST/direct recovery parity, and one forward source path.
The existing compiler has distributed AST and direct recovery owners. Some
ordinary AST paths deliberately retain an incomplete or malformed AST shape
while their direct counterpart emits a `CommittedRecoveryRecord`.

Running a direct owner under `HeaderOutput` while parsing the AST is forbidden:
it reparses the same source and mutates parser transaction state. An AST/CST
walk or a range reparse is forbidden for the same reason. A partial CallTail or
Index-only observer is also insufficient: an embedded `OperatorChain` can
reach canonical statement blocks, declarations, `For`, `Pattern`, and
`TypeExpression` owners.

## 2. Canonical recovery episode

Each semantic recovery owner in the transitive payload closure has one
sink-free episode that determines its owned recovery once:

```text
CanonicalRecoveryEpisode {
  fact: YumarkEmbeddedRecoveryFact,
  continuation: RetrySameSlot | StopAtBoundary | ContinueCloseSettlement
              | MissingAt(position),
}
```

The episode may inspect and consume only the recovery slot's own bytes. It
does not emit CST, build an AST, allocate a diagnostic, invoke public parsing,
or scan source a second time. Shared sequence drivers use child callbacks where
that is the existing owning structure; they are not duplicated AST/direct
loops.

The three participating modes are conceptual, not a new global parser flag:

| mode | action |
| --- | --- |
| `LegacyAst` | preserve the existing ordinary AST contract literally |
| `EmbeddedObservedAst` | call the owner episode once, append its fact to the active persistent Yumark embedded-recovery log, then build the existing AST recovery shape or follow its continuation |
| `Direct` | call the same episode once, create exactly one `CommittedRecoveryRecord` and generic `Missing`/`Error` node, then follow the same continuation |

`EmbeddedObservedAst` is selected only while `YumarkFrame::EmbeddedYulang` is
active. Without that frame, publication is a no-op and ordinary AST input,
shape, remainder, `ErrorSink`, diagnostics, and state remain unchanged.

## 3. Recovery fact identity and transaction

`RecoverySiteSpec { role, expected }` is the common owner descriptor. Its
`expected` is the direct recovery record's primary `ExpectedSyntax`; this
amendment does not introduce an AST contract for a direct record's auxiliary
expectation list. A fact retains:

- `GrammarRole`;
- primary `ExpectedSyntax`;
- range;
- `RecoveryKind`;
- mismatched-close `UnexpectedCategory`, when present.

The existing persistent embedded-recovery log is the only transport. It is
part of the persistent Yumark frame head and therefore participates in all
input/local checkpoints. A rejected speculative owner restores input,
`LineState`, delimiter/layout/stop/ambient frames, persistent recovery head,
`ErrorSink`, output checkpoint, cut, and diagnostic allocation together.

The Yumark AST adapter drains facts in generation order before deciding its
outer wrapper close and assigns one global source order shared with later
Yumark-owned recovery. Direct parsing emits the same facts immediately. No
fact survives an embedded-frame pop.

## 4. Adoption closure

The finite adoption inventory, ordinary witness contracts, primary facts, and
rollback layers are normative in
[`2026-09-02-yumark-gate3b-recovery-adoption-matrix.md`](2026-09-02-yumark-gate3b-recovery-adoption-matrix.md).
It enumerates Expression, Pattern, TypeExpression/polymorphic variants,
canonical Statement, Binding, Use, Mod, Struct, Enum, Error, Type, Role, Impl,
Cast, Act, For, Derives, declaration companion, and the finite Enum/Error
shared-variant cross product. An implementation must adopt every row or prove
that the cited direct committed-record owner is unreachable from its specified
embedded shell; it may not add a new dynamic family boundary.

Root-only recovery, operator-header parsing, public root dispatch, and new
Yumark surface grammar remain excluded. A required outer role remains the
owner selected by that parser; it must not be relabelled as an inner Pattern or
Type primary.

## 5. Invariants

- Every payload byte has one parser-owner invocation in an AST or direct run.
- No shadow direct parse, `HeaderOutput` parse, AST/CST walk, source slice
  reparse, public root recursion, or replay is permitted.
- Each direct record corresponds to one generic direct recovery node. Its
  embedded AST fact has the same primary identity, source range, kind, and
  source order.
- Nested lexical regions and delimiters retain their existing ownership. The
  Yumark wrapper owns only its borrowed outer delimiter and its own recovery.
- Ordinary AST/direct behavior remains literal outside an active embedded
  frame.
- Complexity remains `O(bytes + structural nodes + embedded work)` time and
  `O(structural nesting + live embedded recovery facts)` memory. No timing is
  justified unless an implementation proposes a replay, clone, linear ancestor
  scan, or new cache.

## 6. Gate 3b evidence

The focused isolated AST/direct table must include at least:

1. `\ref(x[,a])`: one `IndexItem` Missing at the comma.
2. `[d]:f(x.)`: one `FieldName` Missing with `Identifier` primary expectation.
3. `\ref(if : x)`: a compound-expression condition recovery.
4. `\ref({@ value})`: a transitive canonical-statement recovery.
5. Pattern, TypeExpression, and every declaration/`For` recovery family
   exactly as listed in the adoption matrix, using the existing exact ordinary
   malformed witness rather than inventing grammar.
6. A mixed nested/outer source proving global recovery order.
7. One rejected speculative owner per recovery layer, proving full transaction
   rollback and preseeded-sink preservation.
8. Ordinary AST/direct controls proving unchanged legacy shape, recovery,
   remainder, and sink behavior.
9. The adoption matrix's committed-recovery → frame-pop → clean-following
   adapter source, proving that a drained fact cannot leak into a later clean
   reference or apply.

Gate 3 remains incomplete until this matrix and the already required Yumark
inline/paragraph/section/list/quote/raw-fence table are green. Gates 4–7 and
root/canonical doc-comment promotion remain out of scope.

## 7. Review and verification

Required implementation delta review:

- compiler/recovery: owner episode identity, continuation, rollback, global
  order, and literal ordinary behavior;
- spec: the Gate 3 allocation amendment plus Yumark addendum §§6.1, 8, 9, and
  11;
- performance only if the implementation proposes work beyond the static
  bounds above.

Verification begins with the named Gate 3 focused table and local owner
controls. Package/workspace suites and timing are deferred to their existing
phase/final gates.
