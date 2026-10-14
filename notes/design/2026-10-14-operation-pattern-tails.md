# Operation patterns: qualified heads and payload calls

Status: Authoritative; user-approved CST/recovery contract.
Approved-by: user
Approved-at: 2026-10-14
Reviewed-by: independent compiler_referee and spec_auditor; accepted admission,
recovery-frontier and diagnostic-ownership findings closed by delta review.
Date: 2026-10-14
Baseline: `21d5a9773e577bf9b49b5d978bc60bedf8d72a42`
Scope: shared Pattern path and glued payload tails, needed for existing Oracle Catch spelling.
Implementation: parser slice complete after focused verification and independent M2 review;
operation-arm HIR/solver construction remains a separate dependent gate.

## User approval

The user replied to the reviewed proposal and explicit approval request:
`まあだいたいこれでいいと思う．あとgitがcleanじゃないのでquestion（回答済み）はもうしまっちゃっていいんじゃないかな`.
This approves the presented shared path/glued-call CST and recovery contract.
The additional request concerns integrating the answered question bundle;
it does not select an unresolved negative-formal field map. No new operation
handler, residual or hygiene semantics are selected by this parser approval.

## Existing behavior and exact missing contract

Frozen Oracle `a58eefc31`, `crates/parser/src/expr/control.rs:815–926` and
`crates/infer/src/lowering/control.rs:1200–1282,1394–1629`, supplies the
operation/payload/raw-continuation spelling and meaning:

```yulang
catch signal::ping():
    signal::ping(), k -> k 1
    v -> v
```

At the pinned baseline the Pattern owner lacks a qualified path tail and a glued call tail.
The shared `PatternMlApplicationTail` already exists under the function-scheme
foundation §§20/41, but needs trivia and respects Catch's `PATTERN_STOP_ITEM`.
Consequently adding a path tail alone does not parse this source. This record
does not change shallow continuation semantics or select another handler syntax.
This record supplies the reviewed, now user-approved CST/recovery contract;
Oracle spelling alone was not its approval.

## Selected proposal

Append `PatternPathTail` and `PatternCallTail` to the syntax-kind vocabulary,
preserving all existing discriminants. Both are children of the ordinary
`Pattern`; there is no Catch-only Pattern wrapper.

```text
Pattern
  IdentifierPattern("signal")
  PatternPathTail
    ColonColon
    Identifier("ping")
  PatternCallTail
    LParen
    RParen
```

Both tails follow any admitted Pattern prefix, matching frozen Oracle
`pat/parse.rs:152,233`. There is no head-shape restriction or eligibility state.
Ordinary identifiers, sigil identifiers, `_`, grouped Patterns and completed
alias/call/path prefixes retain the same tail entry. Path tails permit ordinary
trivia subject to the current frame's layout/fence boundaries. A call requires
glued `(` with no preceding trivia, as in Oracle `pat/scan.rs::read_pat_led_punct`.
Fixed tails are admitted at every existing minimum precedence, including ML
arguments, before alias/alternation/annotation/ML dispatch. Existing terminal
type annotation and protected boundary returns remain terminal.
Catch's `PATTERN_STOP_ITEM` still excludes ordinary ML arguments at its direct
frame; it does not exclude fixed tails. Spaced ML applications retain their
current admission rules.

| Source | Required CST structure |
| --- | --- |
| `A as b::C` | Alias tail followed by a sibling path tail |
| `A(x)::B` | Call tail followed by a sibling path tail |
| `A(x)(y)` | Two sibling call tails |
| `f x::Y` | ML tail whose nested argument Pattern owns the path tail |
| `A (x)` | Existing ML application where permitted; no fixed call tail |

The member after `::` is an ordinary Identifier token, including lexical `_`;
a sigil member enters recovery. Contextual arm guards are preserved as caller
boundaries before identifier admission. Resolution and legal constructor or
operation use remain HIR responsibilities.

Use the existing Pattern delimiter owner/loop for call contents. Empty `()`
is valid, with no missing child. Nonempty contents are ordinary Patterns;
internal commas and the matching close belong to the call. The comma after
the completed call belongs to Catch and introduces the continuation Pattern.
No expression parsing or source-text reparsing is used.

## Recovery proposal

The path member follows Pattern's existing alias-binding identifier-retry
mechanism, with `PatternPathTail` as its immediate CST owner. Its protected
frontier includes caller stops/closes, contextual arm guards, EOF, fences,
layout handoff and fixed Pattern tails (including `::` and a glued call opener).
At a frontier before any malformed input, emit one zero-width Missing and leave
the complete Item/leading pending. Otherwise emit one maximal Error run up to
a valid ordinary identifier or that frontier. Retry a valid identifier in the
same path tail, keeping its leading outside Error. Do not add a same-slot
Missing after Error. Close the path node before resuming sibling tails.

| Input/frontier | Required result |
| --- | --- |
| `A::, k -> b` | Path Missing; comma retained for Catch |
| `A::@ B(), k -> b` | Error `@`, retry `B` with native leading, sibling call, retained Catch comma |
| `A::::B` | First path Missing, second sibling path accepts `B`; incomplete overall Pattern |
| `A::if ...` / `where ...` at an arm guard | Missing; guard retained |
| Protected newline | Missing; whole pending newline/Item retained |
| Permitted deeper continuation newline and identifier | Accept the member under the existing layout policy |
| EOF | One Missing at its boundary |
| Caller-owned foreign close | Missing; close retained |

A retried identifier completes that slot; it does not erase an unresolved
earlier slot. Source containing recovery remains unavailable to the private HIR
carrier under its existing recovery preflight.

Call payloads use an added Call owner in the existing Pattern delimiter loop.
Replace non-close caller stops with local comma/`)` boundaries and retain
carried caller closes. Matching local close has priority over carried close.
Carried foreign caller closes retain their whole pending Item/leading;
uncarried foreign closes use existing Pattern Error consumption. Resume the enclosing
tail loop only after closing `PatternCallTail`.

For these new owners, retain the existing generic structural diagnostic
fallback explicitly:

| Recovery slot | Immediate CST owner | Public projection |
| --- | --- | --- |
| Path member | PatternPathTail | Generic Missing/Error |
| Call element | Nested Pattern | Existing Pattern projection |
| Call separator | PatternCallTail | Generic Missing/Error |
| Call close | PatternCallTail | Generic Missing/Error |

No new mapped slot or Identifier/Pattern/separator/close expectation is claimed.
The total structural walk retains owner, occurrence path, range and recovery
kind. This gate adds no ExpectedSyntax variant or diagnostic adapter. Inspect
`structural_diagnostic.rs`, `diagnostics_schema.rs` and publication consumers
for fallback compatibility; a concrete incompatibility returns to this contract
rather than silently suppressing recovery.

## Implementation and verification boundary

Owning files are `pattern/mod.rs`, `pattern/delimited.rs`, `syntax_kind.rs`
and focused Pattern/Catch tests. Diagnostic/schema owners are inspected for
the explicit fallback contract rather than automatically modified.
`expression/case_like.rs` retains its stop masks. HIR operation resolution,
payload/resumption binding and the residual consumer are separate dependent
work; parsing does not certify them.

M2 contract review: one compiler/recovery referee and one exact-conformance
auditor. Verify recovery-free empty/nonempty payloads, chained paths, following
value arms, internal versus handler commas, nested Patterns, caller Item
preservation, absent members/closes, and foreign-close handoff. Check existing
Pattern/Case/Catch siblings. Preserve one-forward source consumption and
linear structural work. Timing budget: zero; focused verification belongs to
the primary after implementation. The user approval above authorizes this
parser slice and its focused verification.

## Review resolution

The initial proposal's name-head restriction was withdrawn in favor of Oracle's
unrestricted fixed-tail grammar. Member recovery now uses a defined identifier
retry/frontier contract. New owner diagnostics explicitly use the total generic
projection. A final delimiter clarification preserves uncarried foreign-close
Error consumption and retains only carried caller closes. The independent
compiler/referee and conformance delta reviews have no remaining major finding.
Those reviews established proposal readiness. The subsequent approval above
authorized implementation. The
[implementation checkpoint](../progress/2026-10-14-operation-pattern-implementation.md)
records completed parser construction, independent semantic/conformance closure
and focused plus package verification. Private Pattern state retains native
recovery readiness separately from unresolved path members; this implements
the approved distinction without changing existing completion contracts.
