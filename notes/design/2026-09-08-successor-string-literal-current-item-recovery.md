# StringLiteral current-Item typed recovery

Status: Authoritative; private O3b construction pending

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: the non-Rule StringLiteral recovery sites in `rewrite/literal.rs`:
ordinary/heredoc terminator, simple and Unicode escape slots, and interpolation
open/close boundaries. It replaces only their raw Missing publication and the
UnicodeHex raw Error with typed records. Rule DSL literals, VirtualStatementBlock
child recovery, Statement/declaration owners, literal grammar and public
dispatch remain separate.

Authority: typed-output recovery amendment §4's normative literal table and §5;
the literal addendum §4.1 topology/sentinel contract; recovery-authority
amendment §§1--3. Existing roles are sufficient; this makes no vocabulary or
accepted-syntax decision.

## Roles and records

| site | role | expected |
| --- | --- | --- |
| ordinary/heredoc unterminated boundary | `Literal(StringTerminator)` | `Literal(StringTerminator)` |
| backslash without a simple target | `Literal(StringEscapeSimpleTarget)` | escape target |
| Unicode escape without a hex run | `Literal(StringEscapeUnicodeHex)` | Unicode hex digit |
| Unicode escape lacking its required end | `Literal(StringEscapeUnicodeEnd)` | Unicode escape end punctuation |
| interpolation format/open boundary | `Literal(StringInterpolationOpenBrace)` | left brace punctuation |
| interpolation child followed by an absent close at EOF/fence | `Literal(StringInterpolationCloseBrace)` | right brace punctuation |

Each Missing has the mapped role, zero-width site/expectation range, no
unexpected facts, one `COMMITTED_RECOVERY_RULE` expectation and primary index
zero. A malformed UnicodeHex is one sealed Error with the mapped role and one
`OtherCharacter` fact spanning its exact complete nonempty physical run.

## Boundary, extent and child ordering

Use the current inspected/successor coordinate for Missing anchors. Preserve
the existing EOF/fence Item and remainder. An accepted foreign prefix inside a
malformed Unicode run belongs to that Error's physical extent; a deferred prefix
before `%`, quote or `}` remains with the following structural Item. The Error
scan is sealed lexical/literal-only: no grammar parser, nested builder, source
replay, retained vector or CST-derived range.

Virtual child recovery retains its own role and occurs before interpolation
close, then terminator recovery. The interpolation owns borrowed `}` exactly
once as an accepted close; its leading stays outside the child body. Do not scan generically past
that close or relabel remaining Virtual/Rule recovery to StringLiteral.

## Required evidence and execution

Add exact fresh/frozen records for all six roles; empty/valid/malformed Unicode;
run followed by `}`, quote, `%`, EOF or fence; normal/heredoc terminators;
UTF-8 and escaped LF/CRLF; foreign/deferred prefix ownership; shifted anchors;
effect-free rejected opener; actual Expression/Pattern/Rule-string caller
controls and interpolation child/close/terminator ordering. Retain current
literal source/topology tests unchanged.

This is M2: one implementation pass, at most one repair, then specification/
recovery and regression review. Static cost stays O(bytes plus literal
structure), without a new traversal/allocation/replay. Benchmark budget is zero
samples/processes. Synchronize task/index/ledger/daily before commit.

## Construction result

Completed 2026-09-08. All six non-Rule StringLiteral sites publish their typed
records; UnicodeHex uses the sealed lexical Error run. Plain EOF anchors use
the threaded successor while abstract/fence boundaries use their inspected
coordinate. Virtual child recovery remains separate and ordered before String
close/terminator recovery. Focused tests: 8; literal/Pattern/Rule/Virtual/
normalized/recovery-output: 35/54/26/9/83/25; package, format and diff passed.
Specification and regression audits passed after correcting this table's record
labels. Benchmarks: zero samples/processes. Rule DSL and Virtual child recovery
remain open.
