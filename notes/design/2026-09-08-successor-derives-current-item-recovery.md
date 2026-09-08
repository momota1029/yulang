# Derives current-Item typed recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: `rewrite/derives.rs` RoleReference absence and ViaTarget Missing/Error.
No new role, wrapper, separator, delimiter, Statement/root or caller-bypass
policy is added. Declaration body-introducers, companion recovery, Virtual,
Use and public dispatch remain separate.

Authority: recovery-authority amendment §3; typed-output amendment §§4--5;
the C15 derives boundary amendment §§2--3; and the architecture DRV-R table.

## Publication and handoff

RoleReference absence publishes existing
`Declaration(Derives(RoleReference))` / `TypeExpression`, retaining its
existing TypeExpression wrapper. ViaTarget Missing and one maximal lexical Error
publish `Declaration(Derives(ViaTarget))` / `Identifier`, with no new wrapper.
All records have one committed-rule expectation and primary index zero; Missing
is zero-width with no unexpected facts, Error has one `OtherCharacter` fact
over its native emitted lexical run.

The initial malformed ViaTarget leading remains inside its Error, matching the
current owner topology; retry and protected-boundary leading remains pending.
The Error scanner stops before a raw Identifier or a protected C15 boundary.
Boundary classification wins before Identifier retry: contextual
`derives`/`via`/`with`/`impl`, active companion and outer-owned newline return
the exact pending Item/leading with only the completed Error, never a second
ViaTarget Missing. Ordinary EOF anchors Missing at successor after permitted
leading; abstract boundaries use their inspected coordinate; other protected
Items use remaining-start.

The entered Type callee retains its own typed roles; the caller override applies
only to fresh RoleReference absence. Preserve TypeOuterBoundary, all exit
variants, baseline, stops, fence and line handoff. No accepted source changes.

## Evidence and execution

Covered fresh/seeded/frozen records; RoleReference initial/comma absence;
ViaTarget Error/retry and protected contextual/newline boundary after Error;
EOF/fence/close; UTF-8/CRLF/foreign-prefix shifts; nested Type ownership and
Type/Struct/Act/Enum/Error plus companion callers. M1 implementation and
postwrite specification review passed. Derives tests passed 52 and Type tests
196; package check, scoped format and diff passed. Static cost is one forward
lexical scan; benchmark budget remained zero samples/processes.
