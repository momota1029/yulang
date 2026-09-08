# Role current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: raw `RoleDeclarationRole::BodyIntroducer` and inline `Body` recovery in
`rewrite/role_decl.rs`. The already-typed Role Head Type episode, braced and
indented Statement children, caller dispatch and public integration remain
separate.

Authority: recovery authority §3; typed-output §§3--5; architecture `RLD-T`
and `RLD-R`; adoption matrix D3.

## Records and ownership

`Role(BodyIntroducer)` Missing and Error expect ordered `[Semicolon,
Open(Brace), Colon]`, primary zero. These are the full permissible body
starter alternatives; the legacy colon-only Error expectation is rejected as
an incomplete description of the slot. `Role(Body)` expects Statement. Every
record is singleton committed output. Missing has a zero-width site and no
unexpected fact; a maximal lexical Error has one nonempty emitted extent and
one OtherCharacter fact, with every expectation using that same extent and
`COMMITTED_RECOVERY_RULE`.

Role does not admit a punctuation-free body after its head. Head remains the
mandatory Type owner and may retry only at an actual body starter; malformed or
absent Head must not cascade a BodyIntroducer record. Braced and indented body
children, canonical Statement retry, and nested Binding/Pattern/Type recovery
keep their existing owners.

## Boundary, leading and retry

Initial Error leading is emitted by Role, internal run leading by Error, and
retry/protected-boundary leading remains pending. A sealed lexical-only total
Role Item scanner reads each Error run; grammar construction starts only after
the Error closes. A retry starter or canonical Statement is appended outside
Error. Either Error returning a boundary adds no same-slot Missing.

BodyIntroducer ordinary EOF emits residual owner leading before a zero-width
Missing at EOF. Fence, outer close, active stop, layout and ambient boundary
retain the complete pending Item and leading, and anchor Missing at its
remaining-start or at the inspected abstract coordinate. Local starter and
caller/ambient precedence remains Role's existing order.

Inline Body absence, including ordinary EOF, semicolon, comma, close, fence
and outer-owned layout/ambient boundary, retains its complete Item and leading;
its Statement Missing anchors at remaining-start (or inspected abstract
coordinate). The absent body does not consume a semicolon. For a colon followed
by equal-or-shallower newline, first acquire the protected Item, publish Body
Missing at its remaining-start, and preserve the Item's newline, suffix,
successor coordinate and LineEntry unchanged.

## Evidence and execution

Cover exact fresh/frozen records, union order, all starter retries, Error facts,
initial/internal/retry leading, EOF versus fence/outer-close handoff, CRLF
dedent, UTF-8 shifted coordinates, Error-to-boundary no-cascade, missing-Head
no-cascade, child-role ownership, accepted body forms and optional terminal
semicolon. M2 uses one implementation pass and specification/regression
audits, now complete. The static scanner remains O(bytes + structural work);
zero benchmark processes were used.
