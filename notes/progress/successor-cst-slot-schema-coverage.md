# Successor CST slot-schema source coverage

Status: non-authoritative coverage manifest

Date: 2026-09-10

Purpose: reproducibly locate current recovery-publication evidence while the
Draft CST slot-schema catalog is mapped. This is not a grammar schema, a
semantic-slot ledger, parser diagnostic authority, or a public-reference input.
Source sites are evidence links, not slot identity.

## Reproducible census

Run from the repository root:

```sh
rg -n --glob '*.rs' 'emit_recovery_(missing|error_item|error_run)\(|emit_structured_recovery_error_from_item\(' crates/yu-syntax/src | rg -v 'cursor/recovery|src/tests'
```

At this manifest's creation, the command yields 123 matching call sites in 39
source files. That is a publication-site census only: neither number is a
count of semantic slots.

There is one known exception outside this four-emitter census:
`rule/expression_list.rs::emit_leading_newline_separators` calls
`emit_required_slots_before_newlines` with a callback which creates
`ExpressionList(Item)` Missing. It remains an `exception` because it is outside
the four-emitter census. The Rule ExpressionList Draft now supplies direct
caller-specific CST placement/range evidence for the callback's newline phase;
the callback's committed recovery record is still neither slot identity nor a
diagnostic-ledger substitute. It is intentionally excluded from the 123-call
census until a complete catalog row links it.

## Matching rule

Map a source helper/caller to a semantic slot only when the evidence establishes
the same `(production, ordered child phase, necessary ancestor context)` as the
catalog. The helper name, recovery role, parent syntax kind, emitter choice,
or source range alone is insufficient. Record all caller-specific stop,
delimiter/opener, sequence phase, retry, and boundary facts needed to make the
row unambiguous. One helper may contribute evidence to several slots, and one
slot may require several helper/caller sites.

## Manifest status vocabulary

| Status | Meaning |
| --- | --- |
| `untriaged` | census site has not yet been assigned a candidate family/row |
| `candidate` | a likely row exists, but child phase or ancestor context is unproven |
| `linked` | source evidence is linked to a named catalog row; schema facts remain incomplete unless separately marked |
| `delegated` | evidence belongs to a separately named child production/slot |
| `exception` | required recovery evidence intentionally outside the four-emitter census |
| `excluded` | intentionally outside this manifest's source scope |

No status means a call count, file count, or family count equals semantic slots.

## Family-level source coverage

All 39 files below began as `untriaged` evidence links at catalog-scaffold
start. The explicitly linked rows below are bounded exceptions; the groups are
source-navigation families, not semantic schema families.

| Family | Files | Census calls |
| --- | ---: | ---: |
| declarations and headers | 16 | 46 |
| expression forms and tails | 10 | 18 |
| type expression | 5 | 34 |
| pattern | 2 | 8 |
| literal and rule | 3 | 6 |
| root, statement, and virtual layout | 3 | 11 |
| **total** | **39** | **123** |

### Declarations and headers — 16 files / 46 calls

- `crates/yu-syntax/src/declaration/act_decl.rs`
- `crates/yu-syntax/src/declaration/binding.rs`
- `crates/yu-syntax/src/declaration/cast_decl.rs`
- `crates/yu-syntax/src/declaration/declaration_companion.rs`
- `crates/yu-syntax/src/declaration/declaration_variant.rs`
- `crates/yu-syntax/src/declaration/derives.rs`
- `crates/yu-syntax/src/declaration/enum_decl.rs`
- `crates/yu-syntax/src/declaration/error_decl.rs`
- `crates/yu-syntax/src/declaration/fields.rs`
- `crates/yu-syntax/src/declaration/impl_tail.rs`
- `crates/yu-syntax/src/declaration/mod_decl.rs`
- `crates/yu-syntax/src/declaration/operator_header.rs`
- `crates/yu-syntax/src/declaration/role_decl.rs`
- `crates/yu-syntax/src/declaration/struct_decl.rs`
- `crates/yu-syntax/src/declaration/type_decl.rs`
- `crates/yu-syntax/src/declaration/use_decl.rs`

### Expression forms and tails — 10 files / 18 calls

- `crates/yu-syntax/src/expression/case_like.rs`
- `crates/yu-syntax/src/expression/delimited.rs`
- `crates/yu-syntax/src/expression/for_decl.rs`
- `crates/yu-syntax/src/expression/if_expr.rs`
- `crates/yu-syntax/src/expression/required_operand.rs`
- `crates/yu-syntax/src/expression/tails/assignment.rs`
- `crates/yu-syntax/src/expression/tails/colon.rs`
- `crates/yu-syntax/src/expression/tails/fixed_access.rs`
- `crates/yu-syntax/src/expression/tails/inline_slot.rs`
- `crates/yu-syntax/src/expression/tails/with_body.rs`

#### Fixed FieldTail Name and PathTail Segment row links

Only the following verified `fixed_access.rs` locations are linked to the
mapped Draft rows `(FieldTail, required Name immediately after Dot, expression
fixed-postfix continuation context)` and `(PathTail, required Segment
immediately after ColonColon, expression fixed-postfix continuation context)`.
They establish direct wrappers, preserved scanner state, Missing-coordinate
ownership, and shared boundary classification. They do not assign projection,
outer-tail, ML, or nested-child rows.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs:115` | `linked` | FieldTail entry owns direct Dot/name-slot construction and hands incomplete exits to the outer tail |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs:194` | `linked` | PathTail entry owns direct ColonColon/segment-slot construction and hands incomplete exits to the outer tail |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs:325` | `linked` | path payload scanner preserves the returned Item, origin, and line-entry state used by the later handoff |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs:392` | `linked` | shared Missing helper selects the direct zero-width recovery coordinate and preserves protected boundary Items |
| `crates/yu-syntax/src/expression/tails/fixed_access.rs:433` | `linked` | shared fixed-tail boundary classification terminates name/segment admission before outer continuation |

Every other `fixed_access.rs` location remains `untriaged` and unmapped unless
separately linked. These are source-evidence links only; direct Rowan tests and
the governing fixed-tail authority establish the rows' CST and recovery facts.

### Type expression — 5 files / 34 calls

- `crates/yu-syntax/src/type_expr/delimited.rs`
- `crates/yu-syntax/src/type_expr/forall.rs`
- `crates/yu-syntax/src/type_expr/mod.rs`
- `crates/yu-syntax/src/type_expr/record.rs`
- `crates/yu-syntax/src/type_expr/variants.rs`

#### LeadingEffectTypeHead required-head row links

Only the following concrete `type_expr/mod.rs` emissions are linked to the
Draft catalog row `(TypeExpression, required LeadingEffectTypeHead phase
immediately after a direct leading BracketRow)`. Status: `linked`; they
evidence only its incomplete-row/boundary Missing alternatives and direct
malformed Error-run. The row does not assign BracketRow rows, arrow RHS,
structured-primary internals, or another Type context.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/type_expr/mod.rs:1518` | `linked` | incomplete direct leading BracketRow exit publishes the sibling head Missing |
| `crates/yu-syntax/src/type_expr/mod.rs:1667` | `linked` | direct LeadingEffectTypeHead malformed Error-run publication |
| `crates/yu-syntax/src/type_expr/mod.rs:1678` | `linked` | protected-boundary or ordinary-leading direct head Missing publication |

The enclosing helper/caller at `1485–1680` and the focused direct CST/recovery
controls are support evidence, not additional census assignments. In
particular, `[e` proves that the nested BracketRow close Missing precedes the
direct sibling head Missing at the same offset. Every other
`type_expr/mod.rs` emission remains `untriaged` and unmapped unless separately
linked below.

#### BracketRow-selected required-arrow continuation row links

Only the following concrete `type_expr/mod.rs` publishers are linked to the
Draft catalog row `(TypeArrowTail, required-arrow continuation immediately
after its direct BracketRow)`. Status: `linked`; together they evidence the
direct-tail wrapper, completed-row required-arrow classification, the separate
unconditional incomplete-row Arrow Missing/unchanged exit handoff, and
arrowless Type-expression continuation. The row excludes BracketRow internals
and the actual-arrow RHS slot; no other `type_expr/mod.rs` publisher is
assigned to it.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/type_expr/mod.rs:1683–1740` | `linked` | direct `TypeArrowTail` owner; every incomplete BracketRow exit emits its separate Arrow Missing and returns its existing exit/handoff unchanged, without Arrow/RHS classification |
| `crates/yu-syntax/src/type_expr/mod.rs:1780` | `linked` | completed-row boundary, actual-Arrow, malformed-run, and retry classification |
| `crates/yu-syntax/src/type_expr/mod.rs:1850–1854` | `linked` | arrowless admitted-Type leading, its one required-arrow Missing, then `TypeExpression` continuation |

Focused direct CST/recovery support is
`tests/type_expr/bracket_arrow_cst.rs:17–147,151–185,189–408` and
`tests/type_expr/bracket_arrow_recovery.rs:35–100,104–222,226–244`.
This row's existing Draft evidence also establishes same-range nested row-close
then arrow-Missing preorder and a recovered actual Arrow's separate nested RHS
occurrence. Every other `type_expr/mod.rs` emission remains `untriaged` and
unmapped unless separately linked below.

#### TypeArrowTail actual-arrow RHS row links

Only the following source functions are linked to the Draft catalog row
`(TypeArrowTail, required RHS suffix after a direct accepted Arrow)`. Status:
`linked`; they establish the actual-arrow wrapper and RHS owner, plus the
separate BracketRowArrow path that selects this suffix only after accepting an
Arrow. They do not assign the pre-arrow BracketRowArrow slot, BracketRow
internals, or a nested RHS slot.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/type_expr/mod.rs:2430` | `linked` | actual-arrow `TypeArrowTail` wrapper support |
| `crates/yu-syntax/src/type_expr/mod.rs:2466` | `linked` | direct accepted Arrow, RHS Missing/Error/retry/boundary publication and handoff owner |
| `crates/yu-syntax/src/type_expr/mod.rs:1832` | `linked` | direct accepted Arrow selected from the separate BracketRowArrow phase before entering this RHS owner |

The inspected pending-boundary coordinate is temporary parser-record/handoff
evidence only. Future CST-derived projection uses the direct zero-width Rowan
Missing range, which may precede that coordinate at a fence. Every other
`type_expr/mod.rs` emission remains `untriaged` and unmapped unless separately
linked below.

#### TypePathTail required-segment row links

Only the following concrete `type_expr/mod.rs` emissions are linked to the
Draft catalog row `(TypePathTail, required segment immediately after
ColonColon, enclosing Type continuation context)`. Status: `linked`; together
they evidence only this row's three phase-specific Missing alternatives and
its direct malformed Error-run. The Type contextual-boundary correction and
the row's transition facts distinguish same-tail `A::@B` retry from `A::@ B`
handoff to TypeApply; `::` spelling alone is not an assignment rule.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/type_expr/mod.rs:2109` | `linked` | abstract pending-boundary Missing |
| `crates/yu-syntax/src/type_expr/mod.rs:2137` | `linked` | caller/outer protected-boundary Missing |
| `crates/yu-syntax/src/type_expr/mod.rs:2161` | `linked` | ordinary leading/path-boundary Missing after owned leading emission |
| `crates/yu-syntax/src/type_expr/mod.rs:2294` | `linked` | direct TypePathTail malformed Error-run and same-slot retry/handoff evidence |

The helper/caller context at `2074–2273` and `2281–2366` is support for the
linked facts, not a separate census assignment. Every other
`type_expr/mod.rs` emission, including other Type heads, tails, calls, rows,
variants, forall, delimiter, and close contexts, remains `untriaged` and
unmapped.

#### TypeCall terminal-close row links

Only the following census emissions are linked to the Draft catalog row
`(TypeCallTail, terminal close after all argument/separator children, TypeCall
context)`:

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/type_expr/delimited.rs:993` | `linked` | close Error contents |
| `crates/yu-syntax/src/type_expr/delimited.rs:1393` | `linked` | close Missing contexts when `owner == Call` |

Non-census support for that row: close-node wrappers at `1352–1380`, ordinary
EOF completion at `1243–1268`, and dispatch references at `99–213`,
`337–370`, `535`, and `568`, all in
`crates/yu-syntax/src/type_expr/delimited.rs`. These are support links, not
census assignments. Argument/separator emissions and every other owner
emission in this file remain `untriaged` and unmapped.

#### Polymorphic-variant wrong-kind TagName-head row link

Only the following census emission is linked to the Draft catalog row
`(PolymorphicVariantTag, wrong-kind TagName head before payload children,
direct tag in PolymorphicVariantType)`:

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/type_expr/variants.rs:631` | `linked` | structured `Invalid` publication for the wrong-kind TagName head |

Non-census support for that row: outer-list dispatch and fresh-leading entry at
`192–425`; direct-tag wrapper at `546–574`; nested Type entry, non-`TypeApply`
Type-ML scope, and structured extent at `617–678`; returned head/boundary
handoff at `853–900`; malformed-run retry and pending-leading behavior at
`792–850`; and PV boundary ownership at `428–470`, all in
`crates/yu-syntax/src/type_expr/variants.rs`. Direct proof locators are
`tests/type_expr/pv_recovery.rs:263–303`, `tests/type_expr.rs:6735–6832,
7085–7176, 8173–8254`, `tests/type_expr/bracket_arrow_recovery.rs:216–221`,
`tests/type_expr/forall_recovery.rs:496–502`, and
`tests/type_expr/record_field_recovery.rs:368–374`. These are support/proof
links, not census assignments. Malformed prefix, payload/list-tag, separator,
close, and nested Type rows remain unmapped.

### Pattern — 2 files / 8 calls

- `crates/yu-syntax/src/pattern/delimited.rs`
- `crates/yu-syntax/src/pattern/mod.rs`

#### RecordPattern separator-phase structured Invalid row link

Only the existing structured-recovery emission at
`crates/yu-syntax/src/pattern/delimited.rs:500`, in its
`RecordPatternSeparator` separator-phase context, is linked to the referenced
catalog row `(RecordPattern, separator phase, RecordPattern sequence context)`.
Status: `linked`; linked fact: separator-phase `Invalid(Pattern(...))` is
wrapped by the authorized discriminator. Non-census implementation behavior is
support only. The direct item-phase Invalid, its preceding raw Error, and every
other Pattern emission remain unmapped.

### Literal and rule — 3 files / 6 calls

- `crates/yu-syntax/src/literal/mod.rs`
- `crates/yu-syntax/src/rule/mod.rs`
- `crates/yu-syntax/src/rule/expression_list.rs`

#### StringLiteral final outer-terminator row link

Only `crates/yu-syntax/src/literal/mod.rs:849` and
`crates/yu-syntax/src/literal/mod.rs:855` are linked to the Draft catalog row
`(StringLiteral, final outer terminator phase, opener-selected normal/heredoc
mode)`. Status: `linked`; linked facts: the existing boundary path publishes
the `StringTerminator` Missing and returns the protected pending Item. This
evidence link does not classify the temporary shifted recovery record
`105..105` as a schema fact: the isolated interpolation-EOF CST Missing is
`3..3`. All StringPiece/escape/interpolation, Rule, caller, and Root
terminal-leading evidence remains delegated or unmapped.

#### Dedicated Rule-owned row links

Only direct Rule publishers in `crates/yu-syntax/src/rule/mod.rs` are linked to
the six evidence-complete Draft catalog rows below. The shared helper sites are
linked only with their caller contexts; they do not turn a helper or record role
into a slot identity.

| Catalog row | Direct source evidence | Status | Linked fact |
| --- | --- | --- | --- |
| `(RuleBody, final close phase, LBrace-selected Rule body context)` | `250–261` | `linked` | matching close versus direct Body close Missing and returned pending Item |
| `(RuleItem, final parenthesis close phase, RuleItem whose first atom is LParen)` | `474–490` | `linked` | opener-selected matching close versus terminating parenthesis Missing |
| `(RuleCapture, required RHS after Equals, enclosing RuleItem after non-capture postfixes)` | `545–568`, `653–679`, `864–878`, `891–894` | `linked` | terminal Error-to-valid / Error-to-Missing RHS ownership |
| `(RuleField, required name after Dot, RuleItem named-postfix phase)` | `691–720`, `864–878`, `891–894` | `linked` | one-item Error or Missing then outer-RuleItem continuation |
| `(RulePath, required name after ColonColon, RuleItem named-postfix phase)` | `691–720`, `864–878`, `891–894` | `linked` | one-item Error or Missing then outer-RuleItem continuation |
| `(RuleSequence, repeated RuleItem phase, RuleAlternation Body or Parenthesis frame)` | `334–375`, `412–447`, `864–878` | `linked` | repeated direct Error grouping and frame-stop handoff |

`crates/yu-syntax/src/rule/expression_list.rs` is deliberately not linked by
these rows. Its bracket Item/Separator/close slots, plus every RuleCall,
RuleIndex, and bracket-RuleItem caller-specific phase, have bounded Draft
direct-CST evidence but remain unmapped pending complete catalog diagnostic
projection. The special newline callback remains the `exception` above: its
record publication is not slot identity, although the Draft now directly proves
its caller-specific child placement and LF/CRLF ranges.

### Root, statement, and virtual layout — 3 files / 11 calls

- `crates/yu-syntax/src/root_statement.rs`
- `crates/yu-syntax/src/statement.rs`
- `crates/yu-syntax/src/virtual_statement_block.rs`

`rule/expression_list.rs` contributes two census calls and the separate
newline-Missing `exception` above. Its placement in this source-navigation
group does not classify that record-producing callback as a root/layout CST
slot.

## Boundaries

The manifest deliberately excludes `cursor/recovery` implementation sites and
`src/tests` from the census. It does not enumerate non-emitter recovery facts,
direct token construction, public syntax-reference pages, or legacy parser
diagnostic ledgers. A family row becomes useful schema evidence only after the
catalog's required facts and the governing authority have been attached.
