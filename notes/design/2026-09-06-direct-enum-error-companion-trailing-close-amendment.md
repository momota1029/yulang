# Direct Enum/Error companion trailing-close amendment

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-06

Scope: This amendment changes only private direct-rewrite Enum and Error
trailing companion completeness after an actual matching braced variant close.
It retains owner positions, recovery ownership, CST, Enum/Error equals-inline
asymmetry, direct immediate-Item topology, legacy/public separation, and the
atomic final/public gate.

Drafted-by: primary agent

Reviewed-by: independent specification audit

Supersedes: only the recovered-variant/item exclusion for private direct
Enum/Error trailing braced companion positions.

## Decision

After the shared variant-list owner consumes its actual matching `}`, the
concrete Enum or Error owner may attach trailing derives and an exact
contextual `with`, even if recovery was emitted inside that already closed
variant body. Missing, mismatched, or otherwise unconsumed closes remain
ineligible.

The direct shared variant driver intentionally exposes actual close completion,
not nested recovery history. Recovering that history would require an
unauthorized shared completion carrier, stored state, Rowan/CST inspection,
source replay/rescan, or duplicated validation parse. This rule is limited to
the paired private direct slice.

## Retained rules

- Both Header and actual-brace trailing positions may attach for Enum and
  Error; semicolon, colon/equals-indented, missing/mismatched close, terminal,
  caller boundary, fence, and rejected-gap paths do not.
- For EqualsInline only, the shared core yields the exact outer `with` after
  its single local recovery. Enum consumes it immediately as a companion;
  Error returns it unchanged to outer Statement.
- No carrier, new `NormalizedExit` variant, state, inspection, replay/rescan,
  public dispatch, legacy bridge, or shared header abstraction is authorized.

## Required evidence

The paired slice proves clean and recovered actual brace closes, close absence
and mismatch rejection, exact pending Item origin/LineEntry/leading trivia,
CRLF/fence and outer remainder, and all Enum/Error mapping asymmetries. M2
compiler/recovery and specification review remain required before commit.
