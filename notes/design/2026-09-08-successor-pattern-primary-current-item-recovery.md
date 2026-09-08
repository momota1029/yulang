# Pattern primary and tail-slot current-Item recovery

Status: Authoritative; private O3b substep complete

Date: 2026-09-08

Approved-by: user through the current recovery-selection/simplification
delegation; the accepted Pattern grammar is unchanged.

Drafted-and-checked-by: primary under the user's no-subagent instruction.
This is a pre-write contract audit, not independent certification.

Scope: O3b internal substep for `rewrite/pattern.rs` Primary, SymbolName,
AliasBinding and AlternationRhs publication. Delimiter callsites only pass
their existing primary role explicitly; their own slots and literal children
remain later SCC work. Required-Type annotation publication is unchanged.

Supersedes: the architecture's first Pattern recovery table only where an
alternation RHS is called `Missing(Primary)` rather than its named
AlternationRhs slot, and older malformed Pattern retry-leading/layout
behavior as specified below. No accepted-source grammar, precedence, CST
vocabulary, mandatory-slot policy, caller-close or fence contract is replaced.

## Selected rule

Primary and alternation RHS use the existing Pattern grammar, tail threshold,
stop set, mandatory-slot policy, caller-close capability and completion fact.
Publish their own Missing/Error role: Pattern::Primary for an ordinary entry,
Pattern::AlternationRhs for the recursive RHS immediately after a pipe.
Nested accepted owners retain their own roles, including SymbolName,
AliasBinding and TypeAnnotation. Role is an explicit argument, not inferred
from precedence or surrounding CST.

Fresh abstract boundary or fresh-policy stop emits one Missing and returns
the unchanged Item. The existing fresh NUD admission precedes ordinary layout
recovery; do not turn this migration into an accepted multiline grammar
change. Otherwise a local primary boundary emits Missing and returns; a
current tail emits Missing then resumes the ordinary tail judge.

A malformed primary emits one nonempty Error and scans forward one full
current Item at a time. Stop in this order: abstract boundary, fresh-policy
stop, primary/layout boundary, current tail, valid primary retry. The Error
ends before that Item's complete remaining leading. A valid primary retry
emits its leading directly in Pattern, outside Error, then enters the same
primary and recovered-tail policy. A boundary stays complete and pending.
Do not add Missing when the Error itself reaches a boundary.

An accepted `as` owns an ordinary adjacent-or-trivia-separated Identifier
binding, not a sigil name or integer. Fresh admitted identifiers retain their
existing grammar even across a newline; exact `as` is also an ordinary name
in this position. Fresh boundary/current tail produces AliasBinding Missing.
Otherwise emit initial leading directly in PatternAliasTail, then one Error.
During retry, abstract and primary/layout boundaries outrank a valid name;
the name then outranks current-tail classification (so `as` can be the retried
binding). A recovered name's leading belongs directly to PatternAliasTail,
not Error. This fixes only the malformed path that previously consumed a
shallower-line identifier before checking the layout boundary. End the slot
without another Missing if the run reaches a boundary or tail.

SymbolName is an immediate, zero-effect lexical identifier probe after a
committed colon. A miss publishes Missing at the colon's successor coordinate;
there is no skipped run, whitespace scan or SymbolName Error. Contiguous
symbol priority over a colon stop remains unchanged.

Each Missing uses an inspected abstract boundary's coordinate, otherwise the
current Item's remaining-start after permitted owner emission. SymbolName
uses the colon end as above. Missing has no unexpected facts. Each Error uses
its actual contiguous emitted extent and one OtherCharacter unexpected fact
for that opaque malformed run; individual emitted payloads keep native token
kinds. Every record has one same-role/same-range expectation, Pattern for
Primary/AlternationRhs and Identifier for SymbolName/AliasBinding, sources
COMMITTED_RECOVERY_RULE, primary index zero. Error precedes retry-child
records; the node and record are published atomically by existing helpers.

## Concrete pre-write controls

- `@ x`: Primary Error `0..1`, direct Pattern whitespace, then Identifier x;
  the previous Error text `@ ` is intentionally replaced, not blindly updated.
- `A as @ x`: AliasBinding Error `5..6`, direct alias whitespace before x.
- `A as @\nx`: Error `5..6`, pending Identifier x with its entire newline;
  completion remains incomplete. `A as\nx` stays an accepted fresh binding.
- `A |`: AlternationRhs Missing at 3; `A | | B`: RHS Missing at the second
  pipe, then nested alternation. `A | @ :`: RHS Error before the colon tail,
  followed by the distinct required TypeAnnotation record.
- `:` and `: x`: SymbolName Missing at 1; x stays caller-owned in the second
  case. `:x` is accepted with or without a colon stop.
- Caller-owned punctuation, word `in`, raw closes, EOF, quoted fences and
  nonzero UTF-8/CRLF coordinates retain full Item/line/remainder state. Fresh
  and post-Error cases have different node counts, not duplicate Missing.

Retain every existing source literal. Change only assertions of the selected
retry-leading policy, with exact direct-owner trivia assertions. Any other
failure needs causal adjudication before expected-output edits.

Initial construction check: 23/26 existing Pattern tests passed. The three
failures are the already selected retry-leading change for `@ x`, `[a, @ b]`
and `{a: @ p}`. Each Error becomes exactly `@`; the retry gap belongs directly
to its Pattern. The record field's separate first gap stays in
RecordPatternField. No input literal, node count, accepted structure or other
expected output is removed. This paragraph records adjudication before edits.

## Implementation and verification budget

Use M2, primary-only, one implementation pass and at most two repair rounds.
Use sealed Error-run lexical operations, never a general builder/recovery
capability inside the run. The normal and Error scanners share one lexical
current-Item operation. Existing `with_str` already checks same-suffix capture;
use only the transient consumed slice length to advance the explicit origin.
No new chasa-recover API, source retention, replay, Item range field or partial
retry-leading capability is needed. Reuse the existing pure native token-kind
mapping in emit rather than adding another table.

Work remains linear in consumed bytes and structural Items; each loop emits
an Item or returns. Valid paths allocate no recovery storage. Benchmark
budget is zero samples/processes. Test focused exact records, shifted and
seeded/frozen state, symbol-probe rejection, full boundary handoff, malformed
and accepted siblings; then the known-small Pattern/Type/caller/output set
and one package check. Scoped formatting and diff checks close this substep.
No independent review, broad workspace suite, completed SCC/Pattern-owner
claim, O4 certification, header/full/Yumark proof or public cutover is included.

## Construction result

The primary, symbol, alias and alternation sites now publish typed records;
there are zero raw Missing/Error constructors in `pattern.rs`. The eight
caller sites explicitly pass Primary or AlternationRhs; delimiter callers do
not yet select their own element/spread/nested roles. Normal and sealed-run
scans share the same source-free lexical operation using existing `with_str`.
The pure emit token-kind mapping is shared without changing its behavior.
The selected malformed alias layout correction and retry-leading ownership
are implemented. Symbol probes, accepted fresh names and annotation Type
completion remain unchanged.

Seven new tests cover exact complete records and order, shifted coordinates,
prior seeded output, frozen IDs/cursors, direct retry-gap ancestry, native
payload kinds, initial and post-Error caller closes, partially emitted
leading, CRLF/UTF-8, quoted fences, rejected symbol probes and accepted
controls. P1–P4 construction and P8 callee publication are added to the single
ledger. The actual embedded matrix and remaining SCC are not certified.

Checks:

```text
cargo test -p yu-syntax --lib rewrite::tests::pattern:: -- --test-threads=1
target/debug/deps/yu_syntax-b491637626fa8c73 \
  rewrite::tests::type_expr:: rewrite::tests::pattern:: \
  rewrite::tests::type_decl:: rewrite::tests::struct_decl:: \
  rewrite::tests::enum_decl:: rewrite::tests::error_decl:: \
  rewrite::tests::role_decl:: rewrite::tests::impl_decl:: \
  rewrite::tests::act_decl:: rewrite::tests::cast_decl:: \
  rewrite::tests::derives:: rewrite::tests::declaration_variant:: \
  rewrite::tests::normalized::normalized_type \
  rewrite::tests::normalized::ordinary_type_unmatched \
  rewrite::tests::output:: rewrite::tests::recovery_output:: \
  rewrite::tests::binding:: rewrite::tests::for_statement:: \
  rewrite::tests::case_like:: --test-threads=1
cargo check -p yu-syntax
rustfmt --check --edition 2024 crates/yu-syntax/src/rewrite/pattern.rs crates/yu-syntax/src/rewrite/emit.rs crates/yu-syntax/src/rewrite/tests/pattern.rs
git diff --check
```

Pattern 33 passed; expanded owner/output 477 passed, zero failed/ignored,
1.89s execution. Package check passed in 16.16s; scoped formatting includes
the child modules, and diff check passed. Existing 87 package/38 test warnings
remain. Final test build took 1m11s. The new test harness needed two compile
corrections (lifetime/Recoverable import, then explicit RewriteIn type); no
behavioral repair or unapproved expected-output change was made. Primary
delta reread checked all callers and Error capability boundaries, not an
independent review. Benchmark usage: zero samples/processes. Task, design
index, ledger and daily record are synchronized. Next: Pattern delimiters.

Follow-up: `2026-09-08-successor-pattern-delimited-slot-publication.md` now
replaces the five temporary delimiter Primary arguments with their explicit
element/spread/nested roles. The checkpoint description above records this
substep's original boundary, not the current delimiter-role inventory.
