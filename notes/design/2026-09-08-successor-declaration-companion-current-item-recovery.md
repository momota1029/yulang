# Declaration companion current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: all recovery publication in `rewrite/declaration_companion.rs`.
Struct/Type/Enum/Error/Act callers retain their exact `with` judges and
attachment policy; nested Statement/Derives owners, declaration shells and
public dispatch remain separate.

Authority: recovery authority §3; typed-output §§3--5; declaration-companion
addendum DC-R §10; vertical-slices attachment rules.

## Records and leading ownership

| site | role | expectation |
| --- | --- | --- |
| missing/malformed post-`with` introducer | `Companion(Introducer)` | punctuation `:` |
| missing/malformed colon inline item | `Companion(Body)` | Statement |
| braced required/malformed item | `Companion(Item)` | Statement |
| indented required/malformed item | `Companion(IndentedItem)` | Statement |
| missing sequence separator | `Companion(Separator)` | StatementSeparator |
| absent/wrong local brace close | `close(DeclarationCompanion, Brace)` | punctuation `}` |

Every record has one committed-rule expectation and primary index zero. The
legacy Introducer Error's brace-open auxiliary expectation is not carried into
successor output: selected Introducer Missing/Error has only colon expectation.
Missing is zero-width with no unexpected facts. Error has one maximal native
lexical run and one `OtherCharacter` fact over the actual emitted run, except
the close-only Error retains its native close token fact.

Initial malformed leading belongs outside Error at the Companion owner;
internal run leading belongs inside Error; retry and protected-boundary leading
remain pending. An ordinary EOF may emit permitted owner leading then anchors at
successor; fences/outer stops/caller closes use inspected or remaining-start
coordinate with their Item complete. Retry Statement/Derives happens only after
sealed lexical Error closes. Colon requires an item, braces allow empty body;
leading/repeated braced separators publish actual Item Missing, valid trailing
separators publish none. Local wrong `)`/`]` gets one close Error; caller-owned
close remains pending with close Missing and no Item/Body cascade.

## Evidence and execution

Cover all five callers; fresh/seeded/frozen records; comments/CRLF/UTF-8 shifted
ranges; protected fence/stop/close and EOF; layout separators/trailing controls;
retry Statement/Derives and nested ownership. M2 implementation, specification/
recovery and regression audits passed. Companion tests passed 28 and focused
five-caller suites passed; package check, scoped format and diff passed. One
forward lexical scan; zero benchmark processes.
