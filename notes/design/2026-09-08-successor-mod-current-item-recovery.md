# Mod current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: all raw Mod recovery in `rewrite/mod_decl.rs` plus the existing accepted
identity correction that only the first `test` word is a marker. Braced/indented
Statement children, caller dispatch and public integration remain separate.

Authority: recovery authority §3; typed-output §§3--5; architecture Mod
surface/layout/recovery table; adoption matrix D3.

## Records, leading and identity

`Mod(Name/TestName)` expects Identifier. Terminal `Mod(BodyIntroducer)` Missing/
Error expects ordered `[Semicolon, Open(Brace), Colon]`, primary zero; an
admitted Statement lacking a starter has colon-only BodyIntroducer Missing.
`Mod(Body)` expects Statement. Every record is singleton committed output;
Errors are maximal native lexical runs with one OtherCharacter fact. Initial
leading is Mod-owned, internal run leading Error-owned, retry/boundary leading
pending; a terminal Error adds no same-slot Missing.

Name/BodyIntroducer ordinary EOF may emit owner leading before successor Missing;
protected boundary retains whole Item. Inline Body EOF/fence/outer boundary
retains its complete leading and anchors at remaining-start (abstract fence at
inspected coordinate). Colon dedent/equal-indent first acquires its protected
Item, publishes Body Missing at remaining-start, and returns newline/token/
suffix/line entry unchanged. Local inline semicolon remains its existing Mod
terminal behavior.

Only the initial Name slot recognizes `test` as `TestModuleMarker`; TestName
always emits ordinary Identifier, including retry. Thus `mod test test;` has
one marker and one identifier without recovery. Nested child roles remain their
owners.

## Evidence and execution

Cover roles, starters/colon-only, Error retries/boundaries, anonymous/named
test identities, inline EOF/dedent/fence, shifted UTF-8/CRLF, frozen records
and child ownership. M2 implementation and spec/regression audit are complete;
the accepted test-only repair additionally fixes fresh/frozen protected handoff
evidence for payload, leading, line entry, suffix and fence coordinate. One
lexical scan and zero benchmark processes.
