# Authoritative: G4b E5 index ML-application control correction

Status: Authoritative

Scope: the successor rewrite's isolated G4b E5 valid construction witness.
This changes neither production dispatch, recovery adoption, AST parity, nor
unrelated Yumark rows.

Approved-by: user

Approved-at: 2026-09-03

Reviewed-by: M1 scoped specification delta review on 2026-09-03

Supersedes: only the primary E5 witness decision in
`2026-09-03-yu-syntax-g4b-e5-index-call-correction.md` and the corresponding
isolated-rewrite references in
`2026-09-03-yu-syntax-minimal-rewrite-token-transaction-amendment.md`.

## Decision

The primary E5 control is `x[a b]`, not `x[a(b)]`. Its bracket content is
exactly one `IndexItem`: the direct expression headed by `a` accepts the
already-scanned, leading-horizontal-whitespace `Item` for `b` as an ML
argument. It therefore creates one existing `MlArgument` containing the
nested `OperatorChain(b)`. It never creates or recovers an `IndexSeparator`.

The `tail` procedure receives the original owned `Item { leading, payload }`
for `b`. Its local ML predicate recognizes the present narrow witness from
non-empty horizontal whitespace and an identifier core; it neither calls the
scanner nor queries a second lookahead. On acceptance it opens
`SyntaxKind::MlArgument` and moves that Item into the total
`expr_from_core(i, item)` procedure. That procedure emits the Item's owned
leading trivia and text, then scans only its successor.

The child expression returns the same already-scanned `]` as `Err(Left(item))`.
`MlArgument` closes, `IndexItem` closes, and only `IndexTail` validates and
emits that close. No `Recover` field, cursor, context, frame, cache,
delimiter stack, source rescan, separator recovery, Missing, or Error node is
introduced.

The ML child runs with ML continuation disabled, and that capability flows
through every accepted adjacent fixed tail in the child. If it hands a
following Item back, the enclosing ML tail receives that same Item and resumes
its own continuation. Thus the already-governing `f x y` ownership remains
intact: `x[a b c]` has sibling `MlArgument(b)` and `MlArgument(c)`, not a
nested `MlArgument(c)` under `b`; the same remains true after `b(c)` or
`b[c]`. This is the existing handoff rule, not a new layout or recovery
decision.

`x[a(b)]` remains a supplemental control for the ordinary nested `CallTail`:
the call owns `)` and the surrounding index owns `]`. It is not the primary
E5 witness.

This correction is deliberately limited to same-line horizontal whitespace
and identifier cores. Comment/newline layout, other NUD forms, multiple ML
arguments beyond that existing sibling-handoff protection, explicit index
separators, missing closes, and recovery remain at their assigned owners and
are not inferred by this witness.

## Verification boundary

The focused E5 test asserts lossless `x[a b]`, exactly one `IndexTail`, one
`IndexItem`, a direct `OperatorChain(a)`, and one nested `MlArgument` with an
`OperatorChain(b)`. The `]` token is directly owned by `IndexTail`, and the
tree contains no `Missing` or `Error`. The supplemental `x[a(b)]` test keeps
the exact `CallTail` `)` and `IndexTail` `]` owner assertions.

`x[a b c]` is a focused negative topology control: it has two sibling ML
arguments under the item chain and no nested ML argument under either child.
`x[a b(c) d]` repeats that control after an adjacent child `CallTail`.

## Implementation status

Completed on 2026-09-03. The direct rewrite moves the accepted `b` Item into
`expr_from_core` without rescanning it, emits one `MlArgument`, and returns
the same `]` to the surrounding `IndexTail`. The child ML-continuation
capability is preserved through adjacent CallTail and IndexTail paths; only
the enclosing `ml_argument` restores the outer capability after an owned
handoff.

The M1 specification pre-write review required this narrow authoritative
correction. The M1 semantic closure review found two continuation-propagation
gaps (`x[a b c]`, then `x[a b(c) d]`); both were repaired without state,
rescan, or recovery machinery, and the final bounded closure review was clean.
Focused `cargo test -p yu-syntax rewrite::tests -- --test-threads=1` passed
11 tests. `cargo fmt --package yu-syntax -- --check`, `cargo check -p
yu-syntax`, and scoped `git diff --check` passed. No package/workspace suite,
performance measurement, production dispatch, AST parity, or Yumark bridge
ran.
