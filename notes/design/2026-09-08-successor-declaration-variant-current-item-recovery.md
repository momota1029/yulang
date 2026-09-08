# Declaration variant current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: `rewrite/declaration_variant.rs` only. Enum/Error shells, payload field
owners, companion/bypass logic and public dispatch remain separate.

Authority: recovery authority §§1--3; typed-output §§3--4; architecture
ENUM-R and variant sequence rules; the trailing-close amendment.

## Publication and handoff

Use existing roles: `Variant(Item)` for initial/terminal missing item,
`Variant(Name)` when a malformed head retries at an admitted raw Identifier,
`Variant(Separator)` for a missing post-variant delimiter, and
`ClosingDelimiter(EnumBracedVariantBody, Brace)` for an absent braced close.
All Missing records are zero-width singleton committed records; Error has one
maximal native lexical run and one `OtherCharacter` fact.

The lexical run stops before raw-name retry, local separator, qualifying layout,
actual close, caller stop, `with` yield, EOF or fence. Initial leading emits at
the Variant owner; internal leading belongs to Error; retry leading is emitted
by ordinary append outside Error; protected terminal leading stays pending.
Exit selects Name only for admitted raw Identifier, Item otherwise. Nested
payload child recovery keeps its own role. Do not duplicate Item Missing after
an Error terminal, fabricate trailing-separator missing items, or change the
existing Enum/Error `with` asymmetry. Ordinary EOF alone may emit leading before
successor-anchored local Missing; other terminal Items remain whole and pending.

## Evidence and execution

Covered both VariantOwner callers and all four forms; fresh/seeded/frozen records;
retry/terminal Error roles; separator clusters/trailing controls; local/outer
close, `with`, fence, UTF-8/CRLF; child records and effect-free optional shell
rejection. M2: one implementation, at most one repair, then specification and
caller-regression review. One repair added child-role/order and effect-free
optional-shell evidence, and updated only Enum/Error trailing `| with` record
counts from one to zero under the selected no-trailing-Missing rule. Variant
tests passed 23; Enum 17; Error 12; package check, scoped format and diff
passed. One forward lexical scan; zero benchmark processes.
