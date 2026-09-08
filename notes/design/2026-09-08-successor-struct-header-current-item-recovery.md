# Struct header current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: `rewrite/struct_decl.rs` required Struct Name and BodyIntroducer only.
Fields, body constructors, companion routing, derives and trailing attachments
remain separate.

Authority: recovery authority §3; typed-output §§3--5; SD-G/SD-R; Struct
trailing-close amendment.

## Records and leading ownership

Name Missing/Error uses `Struct(Name)` / Identifier. BodyIntroducer Missing and
Error use `Struct(BodyIntroducer)` and the ordered single expectation union
`[Semicolon, Open(Brace), Open(Parenthesis), Colon]`, primary index zero. This
retains the existing selector for both kinds; no single-colon Error policy is
selected.

Name/body Error runs are maximal lexical runs with one `OtherCharacter` fact
over actual native emitted text. Initial malformed leading is emitted at Struct
owner, internal leading belongs to Error, retry/boundary leading remains
pending. Ordinary EOF after an Error preserves its trailing leading outside
Error; only ordinary owner EOF Missing may emit permitted leading before its
successor anchor. Update only header assertions that formerly placed that
trailing whitespace inside Error.

Protected active stop/close/fence/equal-or-shallower newline retains whole
Item/leading. The explicit Struct-owned accepted gap before valid TypePrimary
in `struct S Foo` remains emitted by Struct and reports BodyIntroducer Missing
at the gap; `Foo` stays pending. Error retry to raw name/body starter happens
outside Error; terminal return has no same-slot cascade. Accepted header/body
selection and actual-close trailing attachment remain unchanged.

## Evidence and execution

Cover fresh/seeded/frozen records; four body starters; malformed retry/terminal;
contextual names; active stops/closes/fence; CRLF/deeper/equal indentation;
UTF-8 shifts, `struct S Foo`, EOF leading and effect-free visibility rejection.
M2 implementation and one test-only evidence repair passed specification/
recovery and regression delta review. Struct tests passed 28; normalized Struct
4; package check, scoped format and diff passed. One lexical scan; zero
benchmark processes.
