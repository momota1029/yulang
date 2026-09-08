# Rule DSL literal current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: the ten Rule DSL literal roles owned by `rewrite/rule.rs` and
`rewrite/literal/rule_literal.rs`: Rule body/paren closes, capture/name/path,
unexpected item, RuleLiteral terminator/interpolation close and lazy captures.
It also applies the already-authoritative Body/Paren newline stop before name
admission. StringLiteral, Virtual child, ordinary Rule ExpressionList,
Statement/declaration and public dispatch owners remain separate.

Authority: typed-output amendment §4's normative literal table and category
map; direct-literal cone §4.2's Rule stop/topology contract; recovery-authority
amendment §§1--3. All ten roles already exist.

## Records, stops and retry

Every Missing has its mapped `Literal` role, zero-width range, no unexpected
facts, one committed-rule expectation and primary zero. Only `RuleFieldName`,
`RulePathName` and `RuleUnexpectedItem` emit Error. Each is exactly one lexical
Item with the existing `rule_item_unexpected_category`, one fact over its
emitted range, and no grammar/builder operation inside Error; it then reads the
next current Item and continues its same Rule owner.

RuleBody and RuleParen classify their active newline stop before any identifier
admission. Thus `{a.\nnext}`, `{a::\nnext}` and `{a=\nnext}` leave the
newline/following Item for the caller and publish their mandatory-slot Missing
at the protected boundary. RuleLiteral interpolation deliberately does not
inherit those stops: `|`, `if` and `]` remain its one-item Error controls.

Body/Paren closes, capture right item, terminator, interpolation close and lazy
capture Missing preserve their listed EOF/fence/outer sentinels. Interpolation's
outer quote leading remains in interpolation; an accepted quote is emitted once
by its outer RuleLiteral. Nested String/Virtual and ordinary Rule ExpressionList
keep their own roles.

## Required evidence and execution

Cover all ten fresh/frozen records; body/paren matching close and newline
stops; capture/name/path absence and one-item Error/retry; RuleUnexpectedItem
categories and consecutive Error; terminator/interpolation/lazy EOF/fence;
UTF-8/CRLF/foreign extents; outer quote leading; actual Expression and Pattern
routes; accepted alternatives/lazy/raw capture controls; effect-free rejected
entries. Keep existing source/topology assertions unchanged.

This is M2: one implementation pass, at most one repair, then specification/
recovery and regression review. Static cost remains one Item per Rule Error;
no replay/allocation/traversal is introduced. Benchmark budget is zero
samples/processes. Synchronize task/index/ledger/daily before commit.

## Construction result

Completed 2026-09-08. All ten Rule DSL roles now publish typed Missing or
sealed one-Item Error records. Body/Paren newline stops precede admission while
interpolation retains its intentionally distinct error controls. One repair
anchors ordinary EOF with retained leading at the successor coordinate, leaving
abstract/fence behavior unchanged. Focused Rule tests passed 35; literal 35,
normalized 83 and recovery output 25 passed; package, format and diff passed.
Specification/recovery and regression delta audits passed. Benchmarks: zero
samples/processes. Rule ExpressionList, String/Virtual child and Statement
owners remain open.
