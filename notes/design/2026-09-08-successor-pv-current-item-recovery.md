# Successor polymorphic-variant current-Item recovery

Status: Authoritative; private PV-owned construction complete

Date: 2026-09-08

Scope: private PV-owned recovery in `rewrite/type_expr/variants.rs`, its
current-Item continuation, and typed publication. Shared Type owners remain
responsible for their own nested records.

Approved-by: user through the recovery-selection and simplification delegation
recorded in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary, under the user's no-subagent direction

## Acceptance and supersession

The standalone PV grammar in `2026-08-20-yu-syntax-chasa-architecture.md`
(the polymorphic-variant primary addendum) remains the accepted language:
adjacent `:{`, plain Identifier tags, comma or qualifying newline separators,
and zero or more same-line trivia-separated Type payloads. Payloads use
Type-ML scope, so `:{A Int Bool}` has two sibling payloads. A tag-level newline
always ends the payload sequence; only the tag-list owner judges its indent.
Accepted tight paths and Calls inside a payload retain ordinary Type ownership.

The current recovery authority permits the following bounded simplification:

1. A non-Identifier Type NUD in the tag-name slot is recovered as one full
   Type expression in the existing non-TypeApply Type-ML scope. Its adjacent
   fixed tails stay in that structured TagName Error. The next nonempty
   same-line gap starts a sibling payload. This extends the already-selected
   numeric Call rule to the other wrong-kind heads/tails, and supersedes the
   unimplemented `ReturnPrimary` proposal in
   `2026-09-07-successor-pv-wrong-kind-primary-completion-amendment.md` §§2–3.
   Leading BracketRow follows the existing Type NUD route; it does not need a
   separate scalar admission observer.
2. If a non-NUD malformed Item follows a tag/payload without a same-line trivia
   boundary, return that same Item to the outer tag-list owner immediately.
   It opens one recovered tag and retries a same-line name/Type NUD in that
   tag. This supersedes the old IT-4 empty-gap conditional future-candidate
   scan and PayloadBoundary Error split. For example `:{A@Int}` has tag `A`
   and a recovered tag containing Error `@` then name `Int`; `:{A@}` has tag
   `A` and one malformed tag. Neither needs buffered bytes or replay.
3. With an accepted same-line payload gap, a malformed run stays in one
   payload. It retries the first Type NUD in that payload, or returns the
   first newline, separator, close, EOF, abstract boundary or explicit caller
   stop. The initial gap and retry leading belong directly to the payload;
   neither is included in its Error. Intermediate malformed Items and their
   leading are contiguous Error content.
4. Tag and payload malformed runs share this forward lexical operation.
   Explicit caller stops win before retry after an actual malformed Item,
   including name-shaped stops. The returned Item retains all its un-emitted
   leading. Ordinary fresh name admission and Type contextual scope rules are
   unchanged. The tag-list loop handles the stop immediately after a recovered
   tag, so it cannot consume it on re-entry.

The NT-8 same-slot trivia amendment remains in force. Structured reservation,
outer-before-inner record order, emitted extent validation, native outer closes,
effect-free rejection and frozen reconciliation also remain in force. Actual
ambient-claim adoption, O4/O6 certification and public entrypoints are separate.

## Typed PV sites

All records have their site role/range copied to the single expectation,
`COMMITTED_RECOVERY_RULE` sources and primary expectation index zero. Missing
has no unexpected facts. Error-run/structured TagName evidence is one
`OtherCharacter` Token over the full owned Error range. One-token separator
and close Errors use their actual punctuation category.

| owning procedure / PV1 slot | kind | expected | range / continuation |
| --- | --- | --- | --- |
| tag list, leading/repeated comma | Missing Tag | Identifier | current comma coordinate after locally owned leading; consume comma, slot filled |
| boundary, unfilled post-separator tag | Missing Tag | Identifier | pending Item remaining-start; before the distinct close Missing |
| boundary, missing `}` | Missing ClosingDelimiter(PV, Brace) | Close(Brace) | pending Item remaining-start; inspected abstract-boundary coordinate when present; return Item |
| tag list, local `;` | Error TagSeparator | DelimitedSequenceSeparator | exact token; retry tag-list phase without a tag slot |
| tag list, unclaimed `)` / `]` | Error ClosingDelimiter(PV, Brace) | Close(Brace) | exact token; retry same close responsibility |
| wrong-kind tag | Error TagName | Identifier | emitted nested Type extent; reserve before nested records |
| malformed tag run | Error Tag | Identifier | nonempty emitted run; same-tag retry or boundary handoff |
| adjacent payload NUD | Missing PayloadBoundary | TypePayloadBoundary | NUD start; then parse that payload |
| malformed payload run | Error Payload | TypeExpression | nonempty emitted run; same-payload retry or boundary handoff |

`Tag`, `TagName`, `TagSeparator`, `Payload` and `PayloadBoundary` above are
the corresponding `TypeRole::PolymorphicVariant*` values. No implicit absence
of an optional payload creates a Missing payload. Existing filled/unfilled
tag states and source-bearing CST nodes stay intact.

## Pre-write controls

Offsets are UTF-8 bytes in root Type context. Full-source controls finish at
EOF; appending `::Next` to a matched PV keeps that path outside its Error.

| source | ordered PV-owned records |
| --- | --- |
| `:{,,A}` | Tag Missing `2..2`, `3..3` |
| `:{;A}` | TagSeparator Error `2..3`, unexpected Semicolon |
| `:{]}` | close Error `2..3`, unexpected Close(Bracket) |
| `:{]` | close Error `2..3`, close Missing `3..3` |
| `:{A,` | Tag Missing `4..4`, close Missing `4..4` |
| `:{A\n` | Tag Missing `4..4`, close Missing `4..4` |
| `:{A(Int)}` | PayloadBoundary Missing `3..3` |
| `:{A @ Int}` | Payload Error `4..5`; retry space is payload-owned |
| `:{A @,B}` | Payload Error `4..5`; comma and `B` stay tag-list-owned |
| `:{A@Int}` | Tag Error `3..4`; retry name stays in the second tag |
| `:{123::T}` | TagName Error `2..8` |
| `:{(A)(B)}` | TagName Error `2..8` |
| `:{[e] T}` | TagName Error `2..7` |
| `:{:{A` | outer TagName Error `2..5`, inner close Missing `5..5`, outer close Missing `5..5` |

For `:{@ : rest` and `:{A @ : rest` under explicit `STOP_COLON`, the Error
ends at `@`, the PV close Missing is at the following gap start, and the
complete gap-plus-colon Item is returned with ` rest` still unread. No retry
consumes the colon. Corresponding word-stop, native outer-close, newline,
shifted-origin, comment/Unicode and fenced-prefix controls exercise the same
rule. Exact fresh records are reconciled with distinct frozen IDs; rejection
of mismatched metadata remains discard-only.

## Execution and ledger boundary

M2 private recovery-contract change; direct primary implementation and checking
as requested by the user. One implementation pass and focused repair, no agent
panel. Run new PV typed controls, existing Type/TypeDeclaration and output/RB
filters, then one package check. Record-only updates do not repeat them.

The PV site table is the PV1 callsite ledger for this construction checkpoint;
the focused tests carry the detailed fields and ordinary/RB controls. Aggregate
PV1 certification still needs real embedded/header-full execution at O6.
Other Type owners still contain raw recovery sites and do not become complete
through this change.

The shared run advances one Item per iteration, retaining only the current
Item and two offsets. It has the same linear source work as the existing
separate loops. New allocations are the required typed records and their
single unexpected/expectation arrays, only on recovery. No benchmark decision
depends on timing; budget is zero samples/processes. This grammar-owned rule
does not justify a `chasa-recover` library addition.

## Construction evidence

All PV-owned raw Error/Missing constructions have been replaced by typed
operations. The two malformed-run scanners now share
`recover_polymorphic_variant_run`; both return explicit caller stops before
same-slot retry. The ordinary Type token-kind/evidence classifiers replace the
duplicated PV token-kind table. No new `Item` or library capability was needed.

The site table maps to `type_polymorphic_variant_tags_normalized`,
`type_polymorphic_variant_boundary`,
`type_polymorphic_variant_tag_after_wrong_kind_normalized`,
`type_polymorphic_variant_malformed_tag_normalized`,
`type_polymorphic_variant_payload_normalized`, and
`type_polymorphic_variant_malformed_payload_normalized` in `variants.rs`.
`tests/type_expr/pv_recovery.rs` covers every PV-owned site with complete
records, distinct frozen IDs, node/record range correspondence, accepted
controls, caller Items, shifted origins and native/fenced closes. Existing
structured reservation tests and `rb_pv_rejected_candidate_preservation`
remain passing. Nested non-PV raw sites remain the corresponding Type owner's
next work; this is not aggregate O3a/O6 completion.

Verification: `cargo test -p yu-syntax --lib rewrite::tests::type_expr:: --
--test-threads=1` passed 134 tests. The same built test executable passed
TypeDeclaration 39, output 4 and recovery_output 25 tests. Package check,
scoped rustfmt and diff check passed, with existing warnings only. The first
focused run exposed an off-by-one in the new LF/CRLF test's hand-counted EOF
offset; corrected to the four-/five-byte source lengths without changing code
or the EOF ownership rule. Zero benchmark samples/processes; primary-only
verification under the user's instruction.
