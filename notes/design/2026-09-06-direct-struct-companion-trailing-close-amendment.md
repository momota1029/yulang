# Direct Struct companion trailing-close amendment

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-06

Scope: This amendment changes only the private direct-rewrite Struct trailing
companion completeness rule. It permits an actual matching braced or tuple
close to establish trailing derives/companion authority even when recovery was
emitted inside that already closed field body. It retains all other Struct
attachment positions, direct immediate-Item topology, recovery ownership, CST,
legacy/public separation, and final/public gate requirements.

Drafted-by: primary agent

Reviewed-by: independent architecture, compiler/recovery, and specification audit

Supersedes: only the recovered-close exclusion for the private direct Struct
trailing companion position in the declaration-companion addendum and vertical
slices amendment.

## Decision

The Struct owner may attach trailing derives and an exact contextual `with`
only after its field-list owner consumes the actual matching `}` or `)`.
Recovery already emitted within that body does not independently revoke this
authority. A body with no consumed matching close, including an unclosed or
still-mismatched body, remains ineligible.

This replaces the prior strict interpretation that any recovered field/item
forbids trailing attachment. The current streaming API observes an actual close
but intentionally does not retain nested TypeExpression recovery history.
Recovering that history would require a shared completion carrier, parser
state, Rowan inspection, source replay/rescan, or a duplicate validating parse;
none is authorized by the direct rewrite topology.

## Retained rules

- Header attachment remains complete-name only and ordered `derives*`, exact
  Identifier `with`, then the existing body judge.
- Trailing attachment remains limited to actual braced or tuple closes;
  semicolon/bodyless, indented, missing-close, mismatched-close, terminal,
  caller-boundary, fence, and rejected-gap paths do not attach.
- Struct Header derives retains phase-correct body-starter authority: a fresh
  RoleReference permits `(` as a parenthesized Type primary, while a completed
  outer RoleReference returns `{`, `(`, `:`, and `;` unchanged to the Struct
  body judge. Fresh nested TypeExpression episodes retain `NONE`.
- No shared recovery/completion carrier, new `NormalizedExit` case, stored
  state, Rowan/CST inspection, replay, rescan, or public/legacy dispatch edge
  is permitted.

## Required evidence

The Struct slice must remove any shared recovery-history propagation and cover
clean and recovered actual brace/tuple closes, missing/mismatched closes,
header body starters and nested role distinction, exact pending Item
origin/`LineEntry`/leading trivia, CRLF/fence, outer remainder, and all
existing rejection paths. M2 compiler/recovery and specification review remain
required before commit.
