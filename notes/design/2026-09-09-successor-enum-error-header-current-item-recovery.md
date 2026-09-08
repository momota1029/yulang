# Enum/Error header current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-09

Approved-by: user through the recovery-selection delegation in
`2026-09-08-successor-recovery-authority-amendment.md`

Scope: owner-local Enum and Error declaration Name and BodyIntroducer
publication. Variants/payloads, derives/companion, accepted body forms and the
Enum/Error EqualsInline asymmetry remain unchanged. No shared header abstraction
is introduced.

Authority: ENUM-R/ERROR-R, typed-output §§3--4, recovery-authority §§1--3 and
the trailing-close amendment's no-shared-header boundary.

## Records and no-cascade

Name uses `Declaration(Enum(Name))` or `Declaration(Error(Name))`, expected
Identifier. BodyIntroducer uses the matching owner role and one ordered union:
Semicolon, open Brace, Colon, Equals; every expectation shares the site range
and role, with Semicolon primary index zero. Missing is zero-width/no facts;
Error is the actual nonempty native lexical run with `OtherCharacter` facts.

Initial body punctuation after missing Name produces exactly Name Missing and
the existing body path. A malformed Name run that reaches punctuation returns
it intact and does not retry a body. Preserve sigil terminal controls. Clean
header boundaries remain valid Bodyless with zero BodyIntroducer recovery.
Introducer Error retries an actual starter outside Error or returns a protected
boundary with no second Missing. Child/variant recovery stays native.

## Leading and boundary

Classify abstract/EOF/layout boundary before initial leading emission, but keep
the existing initial body-starter priority over an active stop: actual body
punctuation after missing Name still enters its existing body path. Initial
leading is declaration-owned; internal lexical run leading belongs to Error;
retry leading and protected-boundary leading stay outside Error. Ordinary EOF after Error
emits its remaining leading directly in the declaration and returns EOF with no
second Missing. This narrowly supersedes malformed Error text/parent extent,
but preserves every literal, source coverage, continuation and cardinality.
Do not change inactive-close or lexical scanner policy.

## Evidence

Retain sigil terminal and accepted bodyless/body-form controls. Add paired
Enum/Error exact fresh/shifted/frozen/seeded records, all four starters,
initial/post-run EOF/stop/close/dedent/fence, raw-name retry, UTF-8/CRLF and
foreign-prefix handoff, no-cascade and companion asymmetry controls. M2 with
compiler/recovery and regression review; focused declaration/normalized/output
checks, package/format/diff, zero benchmarks; synchronize records before commit.
