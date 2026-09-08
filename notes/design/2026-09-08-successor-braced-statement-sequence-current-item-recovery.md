# Braced canonical Statement sequence current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: the canonical braced Statement sequence in `rewrite/statement.rs`:
required Statement, post-Statement separator and missing local brace close.
This includes the required-slot separator publication branch exposed by the
current raw retry loop. It does not add role vocabulary or change accepted
grammar. Root/indented Statement, declaration-local recovery and body-introducer
bypasses, VirtualStatementBlock, inherited-close transport, Yumark adoption and
public dispatch remain separate.

Authority: recovery-authority amendment §§1--3 and 5; typed-output amendment
§§3--5; the architecture's canonical braced Statement mandatory-slot/closing
recovery provisions; and the E13/E14 owner evidence. The architecture's
historical unmatched-close consumption is superseded only in this successor
scope by the protected-nonlocal-close rule below.

## Slots, boundary and retry

Use the existing roles only:

| site | role | expectation |
| --- | --- | --- |
| required Statement and malformed Statement run | `BracedStatementBlock(Statement)` | `Statement` |
| missing post-Statement separator | `BracedStatementBlock(Separator)` | `StatementSeparator` |
| absent local `}` | `ClosingDelimiter { BracedStatementBlockExpression, Brace }` | exact `Close(Brace)` punctuation |

Each Missing is a zero-width committed-rule record with empty unexpected facts,
one mapped expectation and primary index zero. A Statement Error is one maximal
nonempty lexical run with native emitted token kind(s) and one `OtherCharacter`
fact over its exact emitted range. Its initial leading is emitted outside Error;
internal run leading belongs to Error; retry/boundary leading remains pending.
No grammar parser or builder runs inside Error beyond the existing sealed lexical
Statement scanner and admission check.

Stop an Error run before an admitted Statement, comma/semicolon, qualifying
newline, matching local `}`, every nonlocal close, EOF or abstract fence
boundary. Retry the same required Statement after Error. A run reaching a
terminal adds no duplicate Statement Missing. In the fresh required Statement
phase, comma/semicolon publishes `Statement` Missing and remains for the
separator owner; it is not Error payload. A post-Statement newly admitted
separate Statement without its required separator publishes `Separator`
Missing. Valid empty bodies, multiline application and valid trailing separator
before a local close or EOF publish no fabricated Statement Missing.

Every nonlocal `)`/`]`/`}` is protected and returned with its entire remaining
Item/leading; this is the selected successor simplification that preserves the
E14 borrowed-close handoff without an inherited-close identity API. Abstract
fences follow the same protected rule and anchor at their inspected coordinate.
An ordinary EOF may emit its remaining leading before publishing the local close
Missing at successor EOF. Local `}` remains emitted by its existing caller.
Preserve suffix, line handoff, baseline, ML mode, sequence context and ambient
barrier through all exits; accepted caller routing and CST wrappers do not
change. Nested children retain their own recovery roles.

## Evidence and execution

Prove fresh and frozen records for Statement Error, Statement Missing,
Separator Missing and close Missing; Error-to-Statement/separator/close/EOF/
fence continuation; repeated separators; valid empty/trailing and ML/Colon
controls; horizontal/CRLF protected nonlocal closes; UTF-8/shifted origins; all
five declaration-body callers; and effect-free optional entry. E13/E14 remain
local owner evidence, not Yumark certification.

M2 used one implementation pass and one repair bundle: qualifying newline
leading now emits before a fresh comma/semicolon Statement Missing hands its
separator to the explicit phase, preventing same-Item nonprogress. The sole
existing expected-output update replaces the obsolete local `]` Error assertion
with the selected protected-close handoff contract. Focused braced tests passed
7; tails 14; Act/For/Impl/Mod/Role 15/12/11/9/15; package check, scoped format
and diff passed. Specification/recovery and regression delta audits passed.
Static cost remains `O(bytes + structural work)` with no replay, run vector or
allocation; benchmark budget remained zero samples/processes.
