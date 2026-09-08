# For structural current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-09

Approved-by: user through the recovery-selection delegation in
`2026-09-08-successor-recovery-authority-amendment.md`

Scope: For Pattern, required `in`, body introducer and post-colon shallow Body
publication. Existing typed Iterable/inline Body, Pattern nested recovery and
IndentedStatement/brace child owners remain unchanged.

Authority: FOR-T/FOR-R, typed-output §§3--4 and recovery-authority §§1--3.

## Slots and records

| slot | role | expected |
| --- | --- | --- |
| initial Pattern | `ForStatement(Pattern)` | Pattern |
| required word | `ForStatement(InKeyword)` | keyword In |
| body starter | `ForStatement(BodyIntroducer)` | primary punctuation Colon; then punctuation open Brace |
| colon plus equal/shallow body line | `ForStatement(Body)` | Statement |

`KeywordEvidence::In` is the finite exact-keyword vocabulary required by the
existing grammar. BodyIntroducer has one node/record and its two ordered
expectations share role and zero-width range; primary is Colon. Every Missing
has no unexpected facts and `COMMITTED_RECOVERY_RULE`. Error has the actual
nonempty lexical run and native `OtherCharacter` facts.

Pattern initial role transport is only for For's initial mandatory slot.
Nested Pattern recovery remains native. A terminal Pattern failure does not
cascade InKeyword/Iterable/BodyIntroducer. Missing `in` at a body starter or
boundary publishes only InKeyword and retries the existing starter route.

## Boundary and retry

Classify abstract boundary, ordinary EOF, separators/active stops, line stop,
unread close and non-NUD opener before emission. Protected Items retain all
remaining leading/payload, suffix, origin and line; ordinary EOF emits the
owner's remaining leading then anchors at EOF. Pattern-valid openers and local
body `{` remain admitted.

BodyIntroducer Error emits initial leading in For and internal leading in
Error, scans lexically until actual eligible `:`/`{` or a protected boundary,
then retries outside Error. Boundary after Error is returned unchanged with no
second BodyIntroducer Missing. The retry predicate and initial predicate agree
on same/shallow line starters. The post-colon shallow branch scans its pending
Statement Item, emits For Body Missing at its inspected coordinate and returns
that Item intact.

No replay, generic API, grammar parser inside Error, operator judge change or
accepted layout change is permitted.

## Evidence

Retain accepted labels/annotated Patterns/body forms and existing For phase
counts. Add exact fresh/shifted/frozen/seeded records; missing/malformed
Pattern, InKeyword and introducer retries; shallow colon Body; EOF/comma/
semicolon/close/opener/fence/foreign-prefix/UTF-8/CRLF handoff; child role
order; actual enclosing continuation; and unchanged optional-label rejection.

M2: one implementation pass, compiler/recovery and regression review, at most
one repair bundle. Focused For/Pattern/normalized/output controls, package
check, format and diff; zero benchmark samples/processes. Synchronize records
before commit.
