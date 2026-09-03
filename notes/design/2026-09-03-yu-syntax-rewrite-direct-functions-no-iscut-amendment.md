# Authoritative: successor rewrite direct functions and no-`IsCut` correction

Status: Authoritative

Scope: `chasa-recover` 0.2 を使う isolated successor rewrite の parser-function
composition と recoverable state に限る。Yulang の表面文法、AST/CST、diagnostic、recovery
role、production dispatch、legacy parser の `IsCut` 所有権は変更しない。

Approved-by: user

Approved-at: 2026-09-03

Reviewed-by: architect audit

Supersedes: `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md` と
`2026-09-02-yu-syntax-expression-tail-handoff-addendum.md` にある successor rewrite
local の `IsCut` preservation requirement のみ

## Decision

The successor rewrite has no `IsCut` capability or shadow state.  Its single
`Recover` object contains immutable root-source and operator-table inputs, plus only
the mutable recovery facts a successor procedure actually reads or writes.  Its
mark snapshots the mutable facts only; immutable inputs neither clone nor roll back.
The legacy parser's own `IsCut` remains with that legacy owner until the legacy
parser is deleted; no old/new bridge, translation, or parity field is added.

Unit-state grammar procedures are ordinary direct functions (or closures which call
them).  They use `chasa_recover` 0.2's blanket `FnOnce(In<I, R, ()>) -> Option<O>`
implementation of `ParserOnce`; the rewrite adds no bespoke `ParserOnce` structs or
implementations unless a later approved capability cannot be expressed as a direct
function.

`In::check` is available from every `S`: it creates only the short `S = ()`
reborrow needed to run the grammar procedure, leaves `S` opaque to that procedure,
and returns its normal result to the direct caller.  This is the ordinary way a
direct committed procedure obtains an Item.  `In::then` remains available for a
parser value that explicitly needs state-lifting composition, but the rewrite does
not use it as routine control flow.

The successor rewrite adds no persistent parser-local frame, stop stack, parent
chain, cache, shadow context, explicit cursor state, Item identity, or scanned-item
history.  Recursive owner calls carry only their immediate scalar arguments;
unclaimed boundaries travel back as the exact existing `Item` via the established
handoff result.  `S` is the direct Rowan sink; every `OperatorChain` is an ordinary
local output value, never an output-stack entry.  Internal `Item`, token, and trivia
records contain ranges and classification facts, not borrowed source slices.  The
final AST keeps its existing source lifetime because its public products borrow
source text.

Leading trivia remains part of its completed `Item` until that Item is accepted or
returned.  An accepting owner moves/emits it once; no procedure clears or replaces
an Item's leading trivia merely to reuse a NUD helper.

In particular, an effect-free entry non-match must classify its raw source before
consuming trivia or mutating recoverable state.  Once classification succeeds, the
direct procedure consumes the already-classified bytes and is total from its local
commit frontier.  A later `None` after consumption is a chasa-recover contract
violation, checked by its existing pointer-index boundary.

## Verification boundary

Focused rewrite evidence retains real recoverable-state, remainder, and committed
Rowan-sink rollback assertions while removing shadow state and scanner-history
assertions.  It includes a leading-trivia non-match control.  G4b remains isolated
and continues to own its direct Item/Separator/Close loop; this correction neither
promotes dispatch nor authorizes a legacy parser call.
