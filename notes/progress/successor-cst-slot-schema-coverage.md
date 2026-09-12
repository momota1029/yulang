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
the four-emitter census, but is now linked to the bounded Rule ExpressionList
catalog row below. Its committed recovery record is neither slot identity nor a
diagnostic-ledger substitute. The caller fence-tree/range proof remains open.

## 2026-09-11 completion-gap audit

The census command still returns 123 sites in 39 files, but it is not yet a
complete publication inventory for ledger-retirement proof. In particular,
`crates/yu-syntax/src/literal/rule_literal.rs` invokes `emit_rule_missing` for
four LiteralRole occurrences and is absent from the four-emitter census/family
table. The RuleLiteralInterpolation frame also reaches shared RuleSequence
Error and child helpers under a distinct ancestor context. These are required
coverage entries, not evidence that the ordinary RuleBody/Parenthesis rows
apply to that frame.

The same audit found several catalog locators under `type_expr/mod.rs` stale
against current source line positions. Existing row statuses are not changed:
the source behavior and topology must be revalidated before adjusting a link.
Until every indirect/helper-mediated publisher and its ordered caller context
is accounted for, this manifest cannot support a complete-schema or
ledger-retirement claim.

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

#### OperatorHeader required-slot Draft links

Only `crates/yu-syntax/src/declaration/operator_header.rs:73–114,261–433` is
linked to the catalog-audited bounded OperatorHeader required-slot Draft: finite
fixity-selected phase order, direct Error/Missing emission, safe-point and
boundary priority, Error-retry/next-phase current-Item preservation,
actual-Equals completion, and terminal pending-Item handoff.
Direct Rowan proof is
`crates/yu-syntax/src/tests/declaration/operator_header.rs:367–536`; it proves
the four slot phases, direct parentage/no Invalid, and the pending safe-point
leading partition. Visibility/lazy prelude, Root body, header facts/conflicts,
fences, and every other declaration/header row remain separate.

#### Cast PatternIntroducer Draft links

Only the required opening-parenthesis introducer immediately after CastKw is
linked. Its CST identity has two authorized shapes: direct CastDeclaration
Missing/Error+ before a CastPattern is admitted, and the initial Missing inside
an implicit `CastPattern(Missing Pattern ...)` for a bare accepted Pattern.
The latter is distinct from a value Missing after native LParen by direct child
position, even though both share a CastPattern parent.

Direct Rowan proof is `cast_pattern_introducer_direct_rowan_slot_order_and_ranges`,
`cast_pattern_introducer_initial_pattern_children_distinguish_value_recovery`,
and `cast_pattern_introducer_rowan_error_group_ends_before_phase_handoff` in
`crates/yu-syntax/src/tests/declaration/cast_decl.rs`. It covers fresh
Missing, terminal Error and its same-line EOF/CRLF partition, Error-to-bare
Pattern retry without duplicate Missing, actual LParen, and Colon/Equals/
Semicolon/close/active-stop handoff. Recovery records and Error spelling are
not used. M1 repair and delta audit were clean. This is a catalog-audited
evidence-complete Draft only for PatternIntroducer; Pattern value/close,
target/form/body, nested Pattern, global interpreter and ledger retirement
remain separate.

#### Cast Pattern value Draft links

Only direct absence after native CastPattern LParen is linked. `LParen Missing
RParen` selects Cast Pattern; colon/semicolon/equals stay native later-phase
evidence, while nonempty malformed Pattern owns its nested Error. Three
`cast_pattern_value_direct_rowan_*` tests in `tests/declaration/cast_decl.rs`
prove order/ranges and terminal boundaries without records or Error spelling.
M1 audit was clean; local-close Error, fence and remaining Cast rows stay open.

#### Cast Pattern close Draft links

The direct terminal CastPattern Missing/Error group after its value maps local
Parenthesis close. Exact `=` now remains form-owned after malformed close;
equals-leading non-form spellings stay whole Error input. Direct
`cast_pattern_close_direct_rowan_*` controls prove ordering, records/frozen
reconciliation and retry ownership without Error spelling. Compiler-referee
repair review was clean; fence and remaining Cast rows remain open.

#### Cast TargetIntroducer Draft links

Only the required colon after a completed CastPattern is linked. Direct
CastDeclaration Missing/Error+ covers EOF, form, outer-boundary and malformed
entry; `CastTarget(Missing TypeExpression)` covers the reusable-Type route
without Colon. The initial CastTarget Missing is separate from a Missing nested
inside TypeExpression, which remains Type-owned. Direct ordered descendants
also retain colon retry, Type retry and native form punctuation outside Error.

Direct Rowan proof is `cast_target_introducer_direct_rowan_slot_order_and_ranges`
and `cast_target_introducer_direct_target_children_distinguish_type_recovery`
in `crates/yu-syntax/src/tests/declaration/cast_decl.rs`. It covers terminal
Error, same-line EOF versus CRLF partition, contiguous multi-leaf Error groups,
colon/Type retry, Semicolon/Equals handoff, unowned RParen and active `else`.
No recovery record, Error spelling or scanner state selects a slot, and no
direct Invalid is admitted. M1 post-write audit was clean. This is a
catalog-audited evidence-complete Draft only for these direct alternatives;
explicit active-RParen, all remaining Cast rows, global interpreter and ledger
retirement remain separate.

#### Cast BodyIntroducer Draft links

Only the required semicolon after completed CastPattern and CastTarget is
linked. Direct declaration Missing/Error+ selects it; native Semicolon is the
bodyless form and native Equals followed by CastBody is the later body form.
A Missing beneath CastBody after Equals is its Body slot, not BodyIntroducer.

Direct Rowan proof is `cast_body_introducer_direct_rowan_slot_order_and_ranges`
and `cast_body_introducer_direct_rowan_excludes_later_body_recovery` in
`crates/yu-syntax/src/tests/declaration/cast_decl.rs`. It covers direct
Missing, terminal/multi-leaf Error with same-line EOF versus CRLF partition,
Semicolon/Equals retry, and protected punctuation outside Error. It uses no
records, Error spelling or scanner state; no direct Invalid is admitted. M1
post-write audit was clean. This is a catalog-audited evidence-complete Draft
only for these alternatives; active-close/fence/UTF-8 extensions, later Cast
rows, global interpreter and ledger retirement remain separate.

#### Cast inline Body Draft links

Only the required inline Expression immediately after direct Cast Equals is
linked. `CastBody` direct Missing/Error+ and retry OperatorChain select Body;
same-line EOF leading is direct body content, while CRLF and protected Items
remain outside. A strictly-deeper indented Statement is a separate owner.
Direct Rowan proof is the three `cast_body_direct_rowan_*` tests in
`crates/yu-syntax/src/tests/declaration/cast_decl.rs`; it uses ordered
parentage/ranges only. M1 post-write audit was clean. Nested Expression,
fence and other Cast rows remain open.

#### ModDeclaration Name/TestName/BodyIntroducer/inline Body Draft links

Only `crates/yu-syntax/src/declaration/mod_decl.rs:76–328,760–894` is linked
to the four bounded direct Mod rows. Rowan child order distinguishes the first
`test` marker from a second ordinary TestName Identifier; the marker's direct
semicolon, braced and Colon starters do not manufacture a second name. After
completed identity, direct Missing/Error and native body starters identify
BodyIntroducer. An actual direct Colon identifies inline Body, whose Statement
child retains nested recovery ownership.

Direct Rowan proof is `mod_schema_identity_slots_have_direct_missing_error_and_identifier_retry`,
`mod_schema_anonymous_test_marker_selects_braced_and_inline_bodies`,
`mod_schema_completed_identity_selects_body_introducer_before_inline_body`,
and `mod_schema_actual_colon_selects_inline_body_and_keeps_child_recovery_nested`
in `crates/yu-syntax/src/tests/declaration/mod_decl.rs`. It covers UTF-8,
CRLF/EOF-leading, terminal/multi-leaf Error, retry leading and child BindingBody
delegation without records, Error spelling or scanner state. M2 spec/regression
audits and the marker-body delta audit were clean. Visibility, braced/indented
children, caller boundaries and all other Mod rows remain separate.

#### RoleDeclaration BodyIntroducer/inline Body Draft links

Only `crates/yu-syntax/src/declaration/role_decl.rs:300–606,790–894` is linked
to the two bounded direct Role body rows. A completed direct TypeExpression
precedes BodyIntroducer; its Missing/Error and native Semicolon/brace/Colon
starters are distinct from actual-Colon inline Body. Absent Head has a nested
`TypeExpression(Missing)` and malformed Head Error is pre-completed-Head
content, so neither is mistaken for BodyIntroducer. A retry TypeExpression owns
its own leading.

Direct Rowan proof is `role_schema_completed_head_selects_body_introducer`,
`role_schema_actual_colon_selects_inline_body`,
`role_schema_incomplete_head_does_not_select_body_introducer`, and
`role_schema_inline_binding_recovery_remains_in_child_body` in
`crates/yu-syntax/src/tests/declaration/role_decl.rs`. It covers UTF-8,
EOF/protected-close/CRLF shape, terminal Error, starter/Statement retry leading
and nested BindingBody delegation without records, Error spelling or scanner
state. M1 post-write specification audit was clean. Head Type recovery,
braced/indented child internals, caller/fence suites and remaining Role rows
remain separate.

#### ImplDeclaration BodyIntroducer/inline Body Draft links

Only `crates/yu-syntax/src/declaration/impl_tail.rs:130–460,760–875` is linked
to these bounded direct Impl body rows. The ordinary first same-line Colon is
inside ImplDescription; its missing or malformed Type is excluded upstream. A
following declaration Colon is the ordinary inline Body path. BodyIntroducer
also has its existing completed-Head body-starter/retry context, so the row is
selected by parentage and child order rather than colon spelling alone.

Direct Rowan proof is `impl_schema_completed_head_or_description_selects_body_introducer`,
`impl_schema_second_colon_selects_inline_body`,
`impl_schema_first_colon_absence_and_malformed_description_stay_upstream`, and
`impl_schema_inline_binding_missing_remains_child_owned` in
`crates/yu-syntax/src/tests/declaration/impl_decl.rs`. It covers UTF-8,
EOF/protected-close/CRLF shape, starter/Statement retries, leading ownership
and nested BindingBody delegation without records, Error spelling or scanner
state. M1 post-write specification audit was clean. Head/Description Type,
braced/indented children, caller/fence suites and remaining Impl rows remain
separate.

#### Enum/Error declaration header Name/BodyIntroducer Draft links

Paired direct Rowan proof in `tests/declaration/enum_decl.rs` and
`error_decl.rs` maps Name Missing/Error/retry and post-name BodyIntroducer
Error/retry. Clean header termination is Bodyless and deliberately has no
BodyIntroducer Missing. All four body starters remain native outside Error.
M1 specification audit was clean; variants, payloads, fields, closes, derives,
companions and caller/fence rows remain separate.

#### StructDeclaration header Name/BodyIntroducer Draft links

Direct Rowan proof in `tests/declaration/struct_decl.rs` maps header Name and
BodyIntroducer by ordered direct Struct children. Semicolon/brace/parenthesis/
Colon starters remain native outside Error; Colon ends the header prefix before
field-owned content. M1 specification audit was clean; fields/body/callers
remain separate.

#### ActDeclaration direct BodyIntroducer/inline Body Draft links

`tests/declaration/act_decl.rs` directly proves completed Head/Source Error,
bodyless exclusion, Colon Body and nested BindingBody separation without records
or Error spelling. M1 specification audit was clean; Derives and child owners
remain separate.

#### DeclarationCompanion direct recovery Draft links

`tests/declaration/declaration_companion.rs` maps six direct roles across five
phase shells and proves seven additional attachment paths with unique `with {}`
wiring. Inline malformed Statement Error remains delegated. M2 spec/regression
and delta audits were clean; nested/caller owners remain separate.

#### UseDeclaration Path/Alias/group-entry Draft links

`tests/declaration/use_decl.rs` maps ordered Path, Alias and group entry/comma
slots, including nested and parenthesized routes and UTF-8. Foreign/local close
have separate rows. The admitted-operator `OperatorName` local Parenthesis close
is separately evidence-complete: direct child order distinguishes it from
missing spelling, and Path/Alias/UseGroup continuations retain their own owner.
The initial direct-UseTree spelling slot is also separately evidence-complete:
`LParen, Missing` distinguishes its Import(Path) expectation from the admitted
operator's local-close Missing, without reclassifying C9 Path failures.
The nested UseGroup item has a separate direct row: same-offset spelling and
group-close/separator Missing occurrences are selected by parent path and
preorder, while foreign-close recovery stays its existing wrapper topology.
Both UseExclusionGroup openers have the corresponding separate inner spelling
row; opener-selected matching/foreign close stays selected by the group rows.
The shared GroupEntry-before-Comma and post-UseTree separator-Missing phases are
also linked for brace and parenthesized exclusion groups, separate from terminal
close and foreign-close rows.
The direct initial GroupEntry Error phase is now linked across braced UseGroup
and both UseExclusionGroup openers. Immediate-parent adjacency combines raw
Error fragments into one occurrence; native trivia, Comma, admitted UseTree and
matching close delimit the run. A foreign close already reached inside that run
stays direct Error, while the separately linked `UseGroupForeignClose` wrapper
continues to identify the later locally consumed close branch.
The corresponding post-child GroupEntry Error phase is separately linked. Its
preceding direct UseTree retains the separator state: a direct UseTree retry is
preceded by the existing Comma Missing, while a native Comma clears it. Matching
close, foreign-close-in-run, UTF-8 trivia and protected semicolon controls fix
the distinct completion and handoff alternatives without relabelling the Error
from Import(GroupEntry)/Path.
The finite UseExclusion dispatcher aggregate is also linked: every occurrence
owns exactly one direct Identifier, Star, OperatorName or UseExclusionGroup
payload. Immediate operator probing distinguishes `(+)` and `(+` from group
forms such as `()`, `(name)` and `( +)`, while all recovery remains delegated
to the selected child. A recursive UseGlob witness establishes the same topology
without promoting the dispatcher into a diagnostic source. Its fresh-admission
trivia exclusion is intentionally bounded: a recovered retry can carry native
leading inside UseExclusion before the same single payload.
The first required-exclusion phase after WithoutKw is now separately linked.
Direct UseGlob Missing/Error project Import(Path)/Path; identifier and
OperatorName retries delegate payload and retry-leading to UseExclusion.
Semicolon, reserved `with` and comma controls preserve three distinct pending
Item/leading states without reclassifying comma as list punctuation.
The repeated exclusion comma loop is linked as one generalized horizontal
Episode rather than ordinal rows. Direct outer Comma/Missing/Error ownership,
two successful repetitions, retry-leading, protected comma/semicolon, nested
group punctuation, OperatorName delegation and normal qualifier termination
compose the established child rows. Newline and complete recursive/fence or
qualifier recovery remain outside this evidence.
The UseQualifiers/UseAnchor/UsePath aggregate is now linked across Version-only,
Anchor-only and combined forms. The nested anchor UsePath owns initial and
post-separator recovery while the qualifier shells remain diagnostic-free.
Ordered Rowan context distinguishes initial Missing/Path, separator
Missing/Identifier and direct Error/Path, including UTF-8 retry and protected
semicolon handoff.
The Realm/Band marker-target dispatcher is now linked. Both markers compose
direct marker token/separator plus group or path target; immediate glob is
evidence-complete only for Band because `realm/*` is lexically a block-comment
start and a spaced Star fails the marker's empty-leading admission. Marker
dispatch stays diagnostic-free and delegates Path/OperatorName or group/glob
recovery to its selected child.
The separate Mod form-head required-path row is now linked. Accepted inline
trivia is direct UseTree content and the following UsePath begins Identifier;
malformed, reserved and protected leading remains path-owned. Initial recovery
and all group/glob/OperatorName tails retain their established owners, so the
repair does not create a new diagnostic source.
The M2 UseGlob aggregate is now linked across bare/repeated aliases, first and
repeated exclusion episodes, interleaved component recovery, nested group/operator
payloads and protected handoff. Alias-only and alias-plus-repeated-exclusion
qualifier returns are direct UseTree sibling closures, including the separate
Band marker caller. The aggregate adds no Glob-wide diagnostic role; newline,
reserved, missing-gap and wider boundary/fence transitions remain unlinked.
M2 specification and regression delta audits for the independent rows were
clean.

#### Use group foreign-close Draft links

`declaration::use_decl::parse_group` now wraps only its existing locally
consumed mismatched-close Error in `UseGroupForeignClose`. Direct Rowan and
fresh/frozen exact-record controls cover UseGroup, both UseExclusionGroup
openers, repeated/mixed directions, RBracket exclusion, UTF-8 leading,
outer/active-stop handoff and accepted groups. Direct GroupEntry Error stays
direct. M2 pre-write and closure audits were clean; the local terminal-close
phase is separately linked below, while OperatorName and the global interpreter
remain separate.

#### Use group local terminal-close Draft links

Only present direct terminal Missing occurrences in `UseGroup` and brace- or
parenthesis-opened `UseExclusionGroup` are linked. The direct opener and
terminal sibling position select Brace versus Parenthesis Close; a native
matching close is the no-diagnostic alternative. This is not a claim that
every group exit has a terminal child: propagated nested-`UseTree` and raw
group-recovery failures remain terminal-child-free.

`crates/yu-syntax/src/declaration/use_decl.rs:920–1052,1677–1691` supplies the
shared phase/publisher, with caller selection at `:397–407,610–620,690–700,
1252–1289`. Direct Rowan proof is the four `use_schema_group_local_` /
`use_schema_group_propagated_` tests in
`crates/yu-syntax/src/tests/declaration/use_decl.rs:575–778`. Their finite
matrix covers all three opener/owner combinations, empty/body/trailing-comma,
earlier GroupEntry/Separator Missing, foreign-close continuation, UTF-8,
matching closes, CRLF caller handoff, both borrowed outer-close directions and
the two no-local-close propagated exits. Classification uses direct ordered
children/ranges and ancestry only. M1 pre-write and post-write specification
audits and the catalog-delta audit were clean. This bounded row is
catalog-audited and evidence-complete within its stated scope. OperatorName,
nested UseTree schemas, additional fence forms, outer Root/Statement
continuation, the global interpreter and ledger/API migration remain separate.

#### Rule ExpressionList direct caller fence Draft links

`tests/rule_expression_list_recovery.rs` proves direct RuleItem/RuleCall/
RuleIndex fence prefixes, matching close Missing and native close controls.
Fence bytes remain outside CST. M1 specification audit was clean; outer Yumark,
pending Item identity and other list slots remain separate.

#### BracedStatementBlock direct raw Error Draft links

`tests/braced_statement_recovery.rs` maps direct block Error groups, retry
Statement, separator/BlockStatementSeparator ownership, UTF-8 and
terminal/protected prefixes without records or Error spelling. M1 specification
audit was clean; Missing/Close and other statement sequences remain separate.

#### ColonApplication indented Statement entry Draft links

`tests/indented_recovery.rs` maps the first required Statement under the full
`ColonApplicationTail > Colon > IndentedStatementBlock` ancestor path. Direct
native leading, zero-width Missing, raw Error token grouping, Statement retry
leading, accepted control and UTF-8/CRLF ranges are covered without consulting
records. M2 pre-write specification and post-write regression/delta audits were
clean. Other transported callers and later/layout/nested slots remain separate.

#### TypeDeclaration DefinitionIntroducer Draft links

Only the completed-name/no-parameter exact-Equals phase is linked. Direct
TypeDeclaration child order distinguishes `Missing` before an admitted RHS,
terminal raw Error and raw Error followed by exact Equals retry; declaration
leading remains outside Error. Direct Rowan proof is
`type_definition_introducer_has_direct_post_name_cst_evidence` in
`crates/yu-syntax/src/tests/declaration/type_decl.rs`, without recovery-record
classification. M1 pre-write and closure specification audits were clean. This
is a catalog-audited evidence-complete Draft only for `type T (A)`, `type T @ `
and `type T @ = A`; parameters, nominal forms, `==`/`=>`, RHS internals,
global interpreter and ledger retirement remain separate.

#### TypeDeclaration equality-RHS fresh required-Type Missing Draft links

Only fresh Type absence after a direct admitted Equals in a structural
TypeDeclaration is linked. `Root > Statement > TypeDeclaration > Equals ...
TypeExpression(Missing)` selects Declaration(Type(Rhs)); the nested empty
TypeExpression separates it from direct DefinitionIntroducer recovery.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/declaration/type_decl.rs:495–538` | `linked` | exact Equals-selected RHS caller and required-Type handoff |
| `crates/yu-syntax/src/type_expr/mod.rs:690–708` | `linked` | caller-role fresh Missing publication inside TypeExpression |
| `crates/yu-syntax/src/tests/declaration/type_decl.rs:139–214` | `linked` | full-shell EOF/protected-Semicolon direct order, ranges, cardinality and handoff without records |

DefinitionIntroducer/Name, malformed/retried/accepted/nested Type, parameters,
nominal forms, other boundary/caller variants, global interpretation and ledger
retirement remain untriaged, delegated or separately linked.

#### TypeDeclaration equality-RHS Type-primary Error Draft links

Only nonempty malformed Type-primary input after the declaration's actual
Equals is linked. `TypeDeclaration > Equals Native* Error+ TypeExpression?`
selects Type(Primary); a following TypeExpression terminates the group and owns
retry leading. DefinitionIntroducer Error and fresh RHS Missing are separate.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/declaration/type_decl.rs:495–538` | `linked` | exact Equals-selected RHS caller and Type exit/handoff |
| `crates/yu-syntax/src/type_expr/mod.rs:732–796` | `linked` | shared Type(Primary) Error publication and TypeExpression retry |
| `crates/yu-syntax/src/tests/declaration/type_decl.rs:217–314` | `linked` | full-shell terminal/retry/protected-Semicolon direct order and ranges without records/Error spelling |

These caller-shell witnesses contain one Error leaf each; shared-publisher
multi-leaf support is linked from the expression annotation row. Fresh Missing,
accepted/nested Type, other boundary/caller forms, global interpretation and
ledger retirement remain untriaged, delegated or separately linked.

#### DerivesClause arbitrary RoleReference-episode repetition Draft links

The Derives RoleReference sequence is one compositional grammar, not a finite
set of ordinal-specific slots. Episode zero follows DerivesKw; every direct
Comma creates exactly one next episode by re-entering the same helper and
boundary policy. An ordinal counts preceding direct commas, not TypeExpression
children. ViaKw terminates this loop and enters the separate ViaTarget row.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/declaration/derives.rs:52–101,105–140` | `linked` | identical initial/post-comma role entry, comma induction step, Via termination and boundary handoff |
| `crates/yu-syntax/src/type_expr/mod.rs:690–708,732–796` | `linked` | fresh TypeExpression(Missing), direct Type(Primary) Error and same-episode retry |
| `crates/yu-syntax/src/tests/declaration/derives.rs:610–1100` | `linked` | bounded base/first-repetition Missing and Error transition cases |
| `crates/yu-syntax/src/tests/declaration/derives.rs:1103–1387` | `linked` | seven compositional rows: consecutive absence, Error/comma, retry/comma, native comma leading, Via transitions and later protected boundary |

The generalized Draft inherits the gap/boundary rules but does not claim full
nested Type, ViaTarget composition, other caller/attachment families,
nonordinary layout/comments/fences, repeated clauses or global interpreter/API
and ledger completion.

#### DerivesClause initial RoleReference fresh Missing Draft links

Only the first required RoleReference immediately after DerivesKw is linked.
`Root > DerivesClause > DerivesKw TypeExpression(Missing)` selects
Declaration(Derives(RoleReference)); post-comma roles and ViaTarget are
separate episodes.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/declaration/derives.rs:105–140,358–371` | `linked` | initial boundary priority, direct TypeExpression/Missing publication and handoff |
| `crates/yu-syntax/src/tests/declaration/derives.rs:610–705` | `linked` | EOF/trivia/RBracket/newline direct order, ranges, unique Missing and complete pending state without records |

Historical spaced-EOF records retain their physical coordinate while Rowan
projection uses the direct Missing range `7..7`. Comma episodes, malformed or
nested Type, ViaTarget, declaration attachments/caller boundaries, other
layout/fence forms, global interpretation and ledger retirement remain
untriaged, delegated or separately linked.

#### DerivesClause post-comma RoleReference fresh Missing Draft links

Only the second RoleReference after one accepted TypeExpression and direct
Comma is linked. `DerivesClause > DerivesKw TypeExpression Comma
TypeExpression(Missing)` selects a distinct occurrence of
Declaration(Derives(RoleReference)) by sibling order and ordinal.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/declaration/derives.rs:72–84,105–140,358–371` | `linked` | direct Comma phase, next required-role boundary and Missing publication |
| `crates/yu-syntax/src/tests/declaration/derives.rs:845–948` | `linked` | EOF/RBracket exact ordered children, ranges, unique Missing and handoff without records |

Initial/further role occurrences, malformed/retried/nested Type, ViaTarget,
attachments/caller boundaries, other layout/fences, global interpretation and
ledger retirement remain untriaged, delegated or separately linked.

#### DerivesClause initial RoleReference Type-primary Error Draft links

Only the initial nonempty malformed required-Type run after DerivesKw is
linked. `DerivesClause > DerivesKw Error+ TypeExpression?` selects
Type(Primary); a retry TypeExpression terminates the direct group and owns its
leading. Fresh initial/post-comma Missing and ViaTarget are separate.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/declaration/derives.rs:52–66,105–140` | `linked` | initial RoleReference caller and Type exit/handoff |
| `crates/yu-syntax/src/type_expr/mod.rs:732–796` | `linked` | Type(Primary) Error publication, retry and terminal boundary behavior |
| `crates/yu-syntax/src/tests/declaration/derives.rs:708–842` | `linked` | terminal/retry/RBracket direct order, maximal group/ranges and handoff without records/Error spelling |

Post-comma malformed/nested Type, other boundaries/layout/fences, ViaTarget,
attachments, global interpretation and ledger retirement remain untriaged,
delegated or separately linked.

#### DerivesClause post-comma RoleReference Type-primary Error Draft links

Only the nonempty malformed second RoleReference after an accepted role and
direct Comma is linked. `DerivesClause > DerivesKw TypeExpression Comma Error+
TypeExpression?` selects Type(Primary); retry TypeExpression ends the group and
owns its leading. Both fresh Missing rows and ViaTarget remain separate.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/declaration/derives.rs:72–84,105–140` | `linked` | post-comma RoleReference caller and Type exit/handoff |
| `crates/yu-syntax/src/type_expr/mod.rs:732–796` | `linked` | Type(Primary) Error publication, retry and boundary behavior |
| `crates/yu-syntax/src/tests/declaration/derives.rs:951–1100` | `linked` | terminal/retry/RBracket direct occurrence, ranges, maximal group and handoff without records/Error spelling |

Initial/later occurrences, nested Type, other boundaries/layout/fences,
ViaTarget, attachments, global interpretation and ledger retirement remain
untriaged, delegated or separately linked.

#### DerivesClause `via` target Draft links

Only `crates/yu-syntax/src/declaration/derives.rs:40–101,144–232,320–356` is linked to
the catalog-audited bounded direct ViaTarget Draft: direct ViaKw dispatch, missing/boundary
priority, raw Error run, Identifier retry and protected-boundary handoff.
Direct Rowan proof is
`crates/yu-syntax/src/tests/declaration/derives.rs:1390–1550`; existing
protected-boundary/retry support is `:1553–1699`. RoleReference Type recovery, comma
repetition, declaration/companion callers, outer stops/fences and all other
declaration/header rows remain separate.

#### BindingBody inline required-expression Draft links

Only `crates/yu-syntax/src/declaration/binding.rs:193–263,331–432,453–560` is
linked to the catalog-audited bounded inline BindingBody Draft: actual-Equals wrapper/branch,
initial Missing, raw Error run, NUD retry, ordinary EOF-leading emission and
protected-boundary handoff. Direct Rowan proof is
`crates/yu-syntax/src/tests/declaration/binding.rs:672–835`; existing
boundary/frozen support is `:42–143,577–668`. Binding target, Equals admission,
indented body, Root progression, fences/active-stop callers and nested expression
recovery remain separate.

#### Shared named declaration-field head Draft links

Only `crates/yu-syntax/src/declaration/fields.rs:555–567,644–950` and its actual
Struct and Enum/Error named-payload callers are linked to the catalog-audited
evidence-complete bounded Name/Colon Draft. Both variant
payloads use `EnumVariant`, enclosed by `EnumDeclaration` or `ErrorDeclaration`.
Initial malformed Name leading is sequence-owned before `StructField` opens;
initial malformed Colon leading is direct field content. Direct Rowan proof is
`crates/yu-syntax/src/tests/declaration/struct_decl.rs:1118–1300` and
`declaration_variant.rs:72–84`; it distinguishes Name recovery before direct
Colon from Colon recovery after direct Identifier and before actual Colon or
Type retry, including Type/Colon retry,
UTF-8/CRLF and dedent handoff. Fresh FieldItem, FieldSeparator, list close,
tuple fields, and the entire required-Type RHS remain separate, including
Type-owned direct Error leaves before optional `TypeExpression`
(`type_expr/mod.rs:640–652,682–726`) and nested Type recovery.
Delta specification audit closed all three record findings without a topology
or implementation change.

#### Shared fresh named declaration FieldItem Draft links

Only the witnessed NeedField comma Missing, malformed-start raw-name retry
and terminal indented dedent paths in
`crates/yu-syntax/src/declaration/fields.rs:371–640,826–868,1190–1219` and
their actual Struct/Enum/Error callers are linked to this bounded Draft. Direct
Rowan proof is `crates/yu-syntax/src/tests/declaration/struct_decl.rs:957–1117`
and `declaration_variant.rs:58–70`; it distinguishes terminal direct
`StructField(Missing)`/`StructField(Error+)` from the mapped Name/Colon head,
then preserves sequence-owned comma/native/Separator recovery and a separate
retried field. Earlier boundary/close/separator dispatch must decline before
malformed-start admission; semicolon and foreign close keep their separate
owners. `Native* Missing` remains a possible shape, but other required-absence
positions and EOF/active-stop variants are outside this evidence. UTF-8/CRLF
dedent handoff is included. Tuple FieldItem,
FieldSeparator, every close, RHS Type, global projection and ledger retirement
remain separate. The direct test audit is clean; catalog delta audit closed
the admission finding for these bounded witnessed alternatives.

#### Shared fresh tuple declaration FieldItem Missing Draft links

Only initial-comma and post-comma EOF NeedField Missing in the shared tuple
sequence are linked to this bounded Draft. Source is
`crates/yu-syntax/src/declaration/fields.rs:371–640,951–979,1190–1219` plus
the required-Type delegation in `type_expr/mod.rs:622–733`. Direct Rowan proof
is `crates/yu-syntax/src/tests/declaration/struct_decl.rs:800–956` and
`declaration_variant.rs:44–56`: it fixes
`StructField(TypeExpression(Missing))`, comma/field order, post-comma EOF
field-before-close preorder, matching-`)` priority, Type-owned `=T` Error and
single-field TypeApply grouping across Struct/Enum/Error. Other absence,
nonempty-leading, active-stop/fence, Type, separator/close, global projection
and ledger retirement remain separate. Direct test audit is clean; catalog
admission wording now preserves preceding boundary/close/comma/separator
dispatch. Catalog delta audit closed that finding.

#### Shared declaration FieldSeparator Missing Draft links

Only the direct zero-width separator Missing after a completed field and before
an admitted same-line successor is linked to this bounded Draft. Source is the
shared sequence in `crates/yu-syntax/src/declaration/fields.rs:371–640,1228–1241`
and its actual Struct/Enum/Error named and tuple callers. Direct Rowan proof is
`crates/yu-syntax/src/tests/declaration/struct_decl.rs:3–147` and
`declaration_variant.rs:28–42`: the Missing is a direct sequence child between
two `StructField` children, with sequence-native gap leading and owner-selected
`Struct(FieldSeparator)` or `Variant(NamedFieldSeparator)`. Fresh FieldItem and
nested field/Type recovery remain independent. Independent catalog audit closed
after correcting the projection input wording and Missing-emitter locator, so
the row is a catalog-audited evidence-complete Draft. FieldSeparator Error is
deliberately excluded from this row. The completed Authoritative
`StructFieldForeignClose` construction removes its former Struct-close
collision, so separate Error and Close rows can now be specified and audited.
Accepted separators, every close, global projection and ledger retirement
remain separate.

#### Shared declaration FieldSeparator Error Draft links

The shared malformed-semicolon run is linked as one maximal adjacent direct
field-list `Error+` group. Struct named, tuple and real colon-introduced
indented lists select `Struct(FieldSeparator)`; Enum/Error named and tuple
payloads select the retained `Variant(NamedFieldSeparator)` role. Direct proof
is `crates/yu-syntax/src/tests/declaration/struct_decl.rs:3–215,559–618` and
`declaration_variant.rs:28–42`; the indented literal fixes Error, retry-leading
and field sibling ranges without recovery-record input. The completed
`StructFieldForeignClose` topology terminates direct groups and distinguishes
adjacent Separator/Close order. Independent catalog audit closed after the row
was corrected to distinguish delimited-only close stops from indented lists,
which have no local close. It is now a catalog-audited evidence-complete Draft.
FieldSeparator Missing, nested field/Type recovery, accepted separators,
all close rows, the interpreter and ledger retirement remain separate.

#### Struct declaration field foreign-close Error Draft links

Only `StructFieldForeignClose(Error+)` under Struct named-brace and
tuple-parenthesis lists is linked. The wrapper is a direct StructDeclaration
child around exactly one unchanged maximal foreign-close run; it emits no
diagnostic, while its immediate Error group projects the opener-selected local
close. Direct proof at
`crates/yu-syntax/src/tests/declaration/struct_decl.rs:218–531` covers the four
former collisions, named/tuple positions, both adjacent orders, multiple and
repeated runs, UTF-8/internal trivia, fresh/frozen equality, active stops and a
direct protected fence. Enum/Error Borrow and real indented Struct are negative
controls. M2 construction review is closed and independent catalog audit was
clean, so this is a catalog-audited evidence-complete Draft. Direct Separator
Error, Close Missing, accepted close,
variant outer close, interpreter and ledger retirement remain separate.

#### Declaration field-list local Close Missing Draft links

The bounded empty-list and tuple post-comma EOF alternatives are linked across
Struct named/tuple and actual Enum/Error variant named/tuple callers. Direct
Rowan proof is `crates/yu-syntax/src/tests/declaration/struct_decl.rs:619–956`
and `declaration_variant.rs:12–56`. Empty lists end `Open Missing` without a
fabricated field; accepted matching closes contain no recovery. At tuple
post-comma EOF, parentage and preorder distinguish fresh
`StructField(TypeExpression(Missing))`, direct local-list Missing, and any later
direct outer declaration Missing at the same coordinate. The opener/list
selects one of the four local Close roles without records. Pre-write,
post-write and independent catalog audits are clean for the EOF slice. The row
now also links `struct_decl.rs:703–799` for Struct active-stop/fence handoff and
`declaration_variant.rs:1209–1288` for named/tuple Enum/Error Borrow, including
one nonempty-leading case. These tests keep Rowan ranges and pending boundary
coordinates separate and inspect no records. Their one unsupported ancestry
assertion was repaired from accepted CST authority and delta review closed.
Independent catalog audit was clean, so the expanded row is a catalog-audited
evidence-complete Draft. Post-comma or
qualifying-newline protected boundaries, other leading combinations, variant
outer close, accepted-close diagnostics, interpreter and ledger retirement
remain outside this row.

#### Braced Enum/Error variant-body outer Close Missing Draft links

Only the braced variant body's direct declaration-owned terminal Missing is
linked. Both EnumDeclaration and ErrorDeclaration select the shared
`EnumBracedVariantBody/Brace` close role. Direct Rowan proof in
`crates/yu-syntax/src/tests/declaration/enum_decl.rs:4–189` and
`error_decl.rs:4–185` covers empty/post-variant EOF, accepted native RBrace,
a foreign RParen with pending CRLF leading, active Colon handoff, quoted fence
and a trailing-comma fence. The Missing is a direct empty shell
child; local payload and fresh field Missing stay below EnumVariant, so equal
offset preorder is structural. There is no outer Close Error path, and accepted
RBrace is only the state delimiter. Pre-write/post-write review and one
test-evidence repair/delta review are closed. Independent catalog audit closed
after correcting the empty-body wording. The boundary extension exposed an
accepted-payload owner bug: caller stops were checked by the sequence but not
before positional/FromType admission. The M2 repair gives variant payload Type
episodes a scoped boundary component, suspends only that component in nested
Arrow RHS, and preserves established ordinary Type-owner boundaries. Direct
payload proof at `declaration_variant.rs:275–423`, Arrow controls, package check
and independent compiler/regression review are clean. This is now a
catalog-audited evidence-complete Draft expanded through those protected
handoffs. Other leading combinations, non-braced forms, remaining nested
variant rows, interpreter and ledger retirement remain outside this row.

#### Declaration Variant core Item, Name and Separator Draft links

Only the direct shared Variant-core Item, Name and Separator alternatives are
linked. `EnumVariant(Missing)` and terminal `EnumVariant(Error+)` witness Item;
`EnumVariant(Error+)` followed by a direct native-leading/Identifier retry
witnesses Name; and the declaration-owned Missing between completed `A()` and
`B` witnesses Separator. Full `EnumDeclaration` and `ErrorDeclaration` shells
are necessary to select their distinct role vocabularies, because `EnumVariant`
alone is shared. Direct Rowan proof is
`declaration_variant_core_slots_have_direct_enum_error_cst_evidence` in
`crates/yu-syntax/src/tests/declaration/declaration_variant.rs`; it
covers braced, inline Equals, indented Colon and indented Equals forms,
UTF-8, terminal raw Error, zero-width Missing and a completed-payload separator
without reading recovery records. M1 pre-write and closure specification audits
were clean, so this is a catalog-audited evidence-complete Draft for those
witnessed alternatives. Payload Type/field/local-close, outer close, terminal
handoff, additional separator-error forms, global interpreter and ledger
retirement remain separate.

#### Declaration Variant `FromType` required-payload Missing Draft links

Only EOF and active-Colon Missing after an admitted direct `FromKw` are linked.
The necessary full Enum/Error shell ancestor and the preceding FromKw select
the owner vocabulary and distinguish `EnumVariant(TypeExpression(Missing))`
from positional payload and field-Type shapes. Direct Rowan proof is
`declaration_variant_from_type_missing_has_direct_enum_error_cst_evidence` in
`crates/yu-syntax/src/tests/declaration/declaration_variant.rs`; it
asserts native initial leading, direct token/node order, source-local empty
TypeExpression/Missing ranges, no Error/Invalid, and an exact pending Colon
Item, leading and remainder. It reads no recovery record for classification.
M1 pre-write and closure specification audits were clean, so this is a
catalog-audited evidence-complete Draft only for those two Missing paths.
FromType Error/retry, all other payload boundaries, positional payload,
fields/closes, global interpreter and ledger retirement remain separate.

#### Declaration Variant `FromType` terminal Type-primary Error Draft links

Only the two full-shell EOF literals with a nonempty malformed primary
immediately after `FromKw` are linked. The direct preceding FromKw, terminal
position and Enum/Error ancestor distinguish the direct `EnumVariant(Error+)`
group from the Variant-core Item Error; the required Type authority assigns it
to Type(Primary), not Variant(FromType). Direct Rowan proof is
`declaration_variant_from_type_terminal_primary_has_direct_enum_error_cst_evidence` in
`crates/yu-syntax/src/tests/declaration/declaration_variant.rs`; it
asserts full ancestry, native token order, source-local Error range and the
absence of TypeExpression/Missing/Invalid without reading recovery records.
M1 pre-write and closure specification audits were clean, so this is a
catalog-audited evidence-complete Draft only for terminal EOF. Retry, caller
boundaries, trailing trivia, other forms, positional payload, fields/closes,
global interpreter and ledger retirement remain separate.

#### Declaration Variant `FromType` Type-primary Error with retry Draft links

Only the exact Enum/Error full-shell `from @ T` retry is linked. Direct FromKw,
the immediate raw Error group and following TypeExpression distinguish the
Type(Primary) occurrence from terminal FromType Error and Variant-core Error;
the retry leading is nested under TypeExpression, not Error. Direct Rowan proof
is `declaration_variant_from_type_primary_retry_has_direct_enum_error_cst_evidence`
in `crates/yu-syntax/src/tests/declaration/declaration_variant.rs`; it asserts
ancestor, token/node order, source-local Error/retry ranges and no
Missing/Invalid without reading records. M1 pre-write and closure specification
audits were clean. This is a catalog-audited evidence-complete Draft only for
the admitted retry; terminal/boundary/trivia/forms, nested Type, other payload
rows, fields/closes, global interpreter and ledger retirement remain separate.

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

#### AssignmentTail direct-inline RHS row links

Only the following verified locations are linked to the mapped Authoritative
catalog row `(AssignmentTail, direct inline required Rhs immediately after
Equals, enabled outer non-ML expression-tail continuation)`. They establish
the direct tail/Equals wrapper and terminal exit, inline RHS
Missing/Error/retry/handoff, shared protected-boundary and leading rule, and
the expression-tail priority that admits Equals only after dynamic LED
declines. They do not assign the left expression, `Assignment(IndentedStatement)`,
any other AssignmentTail context, or nested `OperatorChain` slots.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/tails/assignment.rs:29` | `linked` | direct `AssignmentTail`/`Equals` owner selects inline versus delegated indented RHS and returns the RHS exit after finishing the tail |
| `crates/yu-syntax/src/expression/tails/assignment.rs:90` | `linked` | direct inline Rhs classification owns Missing, maximal raw Error-run, retry to an admitted RHS, and terminal protected-boundary handoff |
| `crates/yu-syntax/src/expression/tails/inline_slot.rs:34` | `linked` | shared inline boundary/leading classification preserves protected Item leading and governs the direct Missing coordinate rule |
| `crates/yu-syntax/src/expression/operator_chain.rs:579` | `linked` | enabled outer expression-tail priority recognizes Equals only after dynamic LED processing has declined it |

Every other emission and helper in `assignment.rs`, `inline_slot.rs`, and
`operator_chain.rs` remains untriaged and unmapped unless separately linked.

#### TypeAnnotationTail required-Type Missing Draft links

Only the exact `as` required-Type absence at EOF and a protected RBracket is
linked. `OperatorChain > TypeAnnotationTail > AsKw > TypeExpression(Missing)`
selects Expression(TypeAnnotation) structurally; the pre-tail whitespace stays
at OperatorChain and the foreign close/leading remains pending. Direct Rowan
proof is `annotation_required_type_missing_has_a_direct_structural_slot` in
`crates/yu-syntax/src/tests/expression_structural_tails.rs`. It asserts direct
token/node order, zero-width ranges and pending handoff without reading records.
`as @` remains Type(Primary)-owned and is excluded. M1 pre-write and closure
specification audits were clean, so this is a catalog-audited evidence-complete
Draft only for the two Missing paths. Type Error/retry, accepted Type, other
boundaries/tails, global interpreter and ledger retirement remain separate.

#### TypeAnnotationTail required-Type primary Error Draft links

Only the nonempty required-Type primary Error immediately after exact AsKw is
linked. `OperatorChain > TypeAnnotationTail > AsKw Error+ TypeExpression?`
selects Type(Primary); the optional TypeExpression terminates the direct Error
group and owns retry leading. The separately linked
`AsKw TypeExpression(Missing)` remains Expression(TypeAnnotation).

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/tails/type_annotation.rs:18–48` | `linked` | exact AsKw caller shell, required-Type delegation and unchanged Type exit |
| `crates/yu-syntax/src/type_expr/mod.rs:732–765` | `linked` | Type(Primary) maximal Error publication, terminal handoff and admitted Type retry |
| `crates/yu-syntax/src/tests/expression_structural_tails.rs:89–248` | `linked` | direct terminal/retry/UTF-8 adjacency, accepted and protected-close Rowan proof; later record/frozen assertions are compatibility-only |

Every other required-Type caller, annotation Missing, nested Type recovery,
unwitnessed boundary/layout form and the global interpreter remains untriaged,
delegated or separately linked.

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

#### NamedRecordType topology construction links

The Authoritative NamedRecordType topology is privately constructed. Its owner
at `crates/yu-syntax/src/type_expr/record.rs:148–276,1088–1110` emits exactly
one `NamedRecordTypeClose` per committed record and wraps only existing
Separator Missing/Error publications in `NamedRecordTypeSeparator`; Field/Name
recovery remains direct. The committed-close abstract-boundary guard preserves
the protected Item before token classification. Direct proof is
`crates/yu-syntax/src/tests/type_expr/record_sequence_recovery.rs:39–615`, with
dependent ancestry controls in `record_field_recovery.rs`, `tests/type_expr.rs`
and `tests/pattern.rs`. The focused proof covers Field/Close separation,
separator leading/cardinality, accepted close, EOF/fence/current-Item and
fresh/frozen records. This is a topology construction link, not a completed
semantic diagnostic-row mapping; PV and remaining NamedRecord semantic slots
remain separate.

#### NamedRecordType semantic-slot Draft links

The six direct semantic slots are now linked only for their witnessed forms:
whole-field `Missing`/raw `Error` directly under `NamedRecordType`; Name,
Colon and RHS Type in ordered `TypeRecordField` children; recovery-only
`NamedRecordTypeSeparator`; and the unique committed
`NamedRecordTypeClose`. The direct Rowan proofs are
`record_field_cst_orders_name_colon_and_type_recovery_without_ledger_context`
and `record_sequence_cst_occurrences_distinguish_field_separator_and_close` in
`crates/yu-syntax/src/tests/type_expr/record_field_recovery.rs` and
`record_sequence_recovery.rs`. They fix no-cascade Error-to-Type retry,
nested Type ownership, Field/Separator/Close collision splits, terminal-close
cardinality and equal-offset nested Close occurrence paths without reading
records, Error spelling, green identity or ranges as identity. Post-write
specification and recovery audits are clean. Status: `evidence-complete Draft`
for Field, Name, Colon, Type, Separator and Close over those forms only;
remaining boundary/trivia alternatives, PV, all other Type rows, the global
collector and ledger/API migration remain open.

#### PolymorphicVariantType foreign-close topology construction links

The Authoritative PV topology is privately constructed at
`crates/yu-syntax/src/type_expr/variants.rs:253–279`. Only the locally consumed
foreign `RParen`/`RBracket` Error emission is wrapped in
`PolymorphicVariantForeignClose`; direct semicolon Separator Error and all
other PV owners remain direct or nested as before. Direct proof is
`crates/yu-syntax/src/tests/type_expr/pv_recovery.rs:199–689`, with dependent
payload/outer-close ancestry controls in `tests/type_expr.rs`. It covers
positions, repetition, mixed groups, leading, fence/caller handoff, tail and
fresh/frozen records. This topology evidence remains distinct from the bounded
PV semantic-row links below.

#### PolymorphicVariantType semantic-slot Draft links

The bounded PV rows are linked for direct Tag Missing/Error, the already-mapped
TagName Invalid dependency, PayloadBoundary/Payload, direct Separator groups,
and terminal or `PolymorphicVariantForeignClose` Close occurrences. Direct
Rowan proof is `pv_semantic_missing_slots_use_direct_ordered_siblings` and
`pv_semantic_error_slots_use_direct_groups_and_ancestry` in
`crates/yu-syntax/src/tests/type_expr/pv_recovery.rs`. The tests use complete
ordered sibling context for Tag versus Close, preserve separate repeated
ForeignClose occurrences, and retain adjacent raw separator Errors as one
semantic group even where temporary records are more numerous. Retained tests
cover UTF-8 ranges, retry/no-cascade, boundary handoff and nested Type
ownership. Pre-write and post-write specification audits are clean. Status:
`evidence-complete Draft` only for these witnessed PV-owned rows; other PV
forms, nested Type schemas, the global collector and ledger/API migration
remain open.

#### ForallType direct-head composition Draft links

The aggregate row composes the three phase-local Forall rows below with the
previously excluded first actual-binder gap, recovered binders across covered
Colon recovery, repeated separator placeholders and conditional terminal
forms. It is one finite state machine over the unchanged iterative head loop,
not a binder-ordinal enumeration and not a new Rowan wrapper.

The driver is `crates/yu-syntax/src/type_expr/forall.rs:56–115,142–542`.
Direct composition proof is the three `forall_head_composition_*` tests at
`crates/yu-syntax/src/tests/type_expr/forall_recovery.rs:96–264`, together with
the existing phase-local tests below. The long witness crosses first-binder
Error, actual-binder gaps, two separate separator placeholders, repeated
direct Colon Error groups, actual Colon, Body Error and TypeExpression retry.
Terminal variants show that a covered Colon stays covered across later binders
and boundary leading remains outside the Forall node; five shorter controls
fix current-slot-only terminal recovery and no cascades. Projection uses direct
wrapper contents, parentage, sibling order and ranges only. M1 pre-write and
post-write and catalog-delta specification audits were clean after correcting
the catalog's phase-specific leading-owner wording. The aggregate Draft is
catalog-audited and evidence-complete within its stated scope. Nested Type,
broader caller/fence paths, public/header/Yumark use, the global interpreter and
ledger/API retirement remain separate.

#### ForallType first required-binder candidate links

Only `crates/yu-syntax/src/type_expr/forall.rs:56–74,142–258,269–315,319–381,
498–542` is linked to the bounded first-binder candidate: ForKw/head phase,
priority, maximal raw run and direct Missing publication. Direct Rowan proof is
`forall_semantic_binder_slots_use_only_direct_wrapper_order` in
`crates/yu-syntax/src/tests/type_expr/forall_recovery.rs`; later binder,
colon/body, nested Type and every other forall emission remain separately
unmapped.

#### ForallType later BinderBoundary candidate links

Only `crates/yu-syntax/src/type_expr/forall.rs:142–258,326–357,379–381,
498–542` is linked to the bounded later BinderBoundary candidate: accepted
binder advancement, grammar-empty Missing inside the next binder, one-item
separator placeholder Error and successor dispatch. Direct Rowan proof is
`forall_semantic_binder_boundary_occurrences_keep_sibling_order` in
`crates/yu-syntax/src/tests/type_expr/forall_recovery.rs`. The first
binder, colon/body, other malformed head content, nested Type and caller
boundary handling remain separate rows.

#### ForallType terminal emitted-colon/body candidate links

Only `crates/yu-syntax/src/type_expr/forall.rs:142–258,269–315,407–496,
498–542` is linked to the bounded emitted-colon/body candidate: terminal
colon classification, direct colon/body Missing, direct raw Error retry and
protected body handoff. Direct Rowan proof is
`forall_semantic_terminal_slots_use_direct_colon_order_and_ranges` in
`crates/yu-syntax/src/tests/type_expr/forall_recovery.rs`. The lexical
ordinary/polymorphic-variant-colon distinction is intentionally not a separate
row because both emit `SyntaxKind::Colon`; recovered binders, first/later binder
phases, nested Type and caller-boundary handling remain separate rows.

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

#### TypeCallTail direct production composition Draft links

Six `type_call_repetition_*` tests in
`crates/yu-syntax/src/tests/type_expr/type_call_fallback.rs:32–326` compose the
three audited phase rows below. They cover Comma/Semicolon repetition,
same-slot Error retry, zero/trailing close bypass, same-offset item-before-close
Missing, inherited separator Missing, ordinary-layout and pipe-special item
Error, residual close recovery and protected-stop handoff. Exact direct
node/token identity, parents, ranges and one terminal TypeCallClose are asserted
without record or Error-spelling classification. M2 pre/post specification and
compiler reviews and the catalog-delta audit are clean after one evidence-only
helper repair and an ordinal-wording correction. The aggregate Draft is
catalog-audited and evidence-complete within its stated scope; nested Type and
global interpreter/API/ledger work stay separate.

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

#### TypeCall CallArgument item-phase candidate links

`crates/yu-syntax/src/type_expr/delimited.rs:108–130,568–609,814–931,1164–1176`
is linked as the CallArgument entry, boundary and Error-retry evidence. Direct phase/order proof is
`crates/yu-syntax/src/tests/type_expr/type_call_fallback.rs:120–206`; broader
existing missing/retry/boundary/fence controls are cited in its candidate
catalog row. This is an evidence-complete candidate only: separator, close,
caller and nested Type rows remain separately owned and unmapped here.

#### TypeCall separator-phase links

`crates/yu-syntax/src/type_expr/delimited.rs:73–79,360–507,1140–1210,1299–1330`
and `type_expr/mod.rs:2883–2888` are linked to the bounded separator row.
Direct accepted/inherited-ML/error-discriminator/frozen proof is
`crates/yu-syntax/src/tests/type_expr/type_call_fallback.rs:52–218`; boundary
support remains separately cited by the catalog row. The mapped row excludes
CallArgument, TypeCallClose and nested Type ownership.

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
`crates/yu-syntax/src/type_expr/variants.rs`. Direct proof is
`pv_semantic_error_slots_use_direct_groups_and_ancestry` in
`tests/type_expr/pv_recovery.rs`, with the listed retained recursive controls
as support. These are support/proof links, not census assignments. The bounded
PV semantic Draft now maps the witnessed malformed prefix, payload/list-tag,
separator and close forms; other PV and nested Type rows remain open.

### Pattern — 2 files / 8 calls

- `crates/yu-syntax/src/pattern/delimited.rs`
- `crates/yu-syntax/src/pattern/mod.rs`

#### Pattern SymbolName Missing Draft links

Only the immediate post-colon absence at EOF and pending-Identifier control are
linked. `Pattern > SymbolPattern > Colon Missing` selects Pattern(SymbolName)
without conflating annotation or other colon occurrences; `: x` leaves `x` and
its leading space pending for its caller. Direct Rowan proof is
`symbol_name_missing_has_a_direct_colon_successor_slot` in
`crates/yu-syntax/src/tests/pattern/recovery.rs`; it asserts parentage,
token/node order, zero-width range and handoff without reading records. M1
pre-write and closure specification audits were clean. This is a
catalog-audited evidence-complete Draft only for these two witnesses; accepted
symbols, other primary/tail/delimited recovery, global interpreter and ledger
retirement remain separate.

#### Pattern AliasBinding Missing and Error Draft links

Only the immediate `as` binding absence, raw-error retry and terminal raw-error
alternatives are linked. `Pattern > PatternAliasTail > AsKw` and the ordered
direct recovery children select AliasBinding; pre-`as` whitespace remains
outside the tail, while initial/retry leading is tail-native rather than Error.
Direct Rowan proof is `alias_binding_recovery_has_a_direct_ordered_tail_slot`
in `crates/yu-syntax/src/tests/pattern/recovery.rs`; it asserts direct shape,
ranges, terminal cardinality and no record-based classification. M1 pre-write
and closure specification audits were clean. This is a catalog-audited
evidence-complete Draft only for `A as`, `A as @ x`, and `A as @`; layout and
boundary variants, all other Pattern rows, global interpreter and ledger
retirement remain separate.

#### Shared initial Pattern Missing and Error Draft links

The shared initial kernel now has direct Rowan-only evidence for its finite
transported-role table: ordinary Primary, AlternationRhs, the five delimited
element/spread/nested slots, Binding Target, For Pattern, Case/Catch first
Pattern, and Catch handler Pattern after its native comma. The direct Pattern
prefix selects a zero-width Missing or a maximal direct Error group; retry
leading is native direct Pattern content and an admitted primary is distinct
from that group. Caller context and ordered children, rather than Error
spelling or recovery records, select the role.

`crates/yu-syntax/src/tests/pattern.rs` proves all Missing, terminal Error and
Error-to-retry alternatives through actual caller shells. It also pins
UTF-8/CRLF ranges, the protected For `in` handoff, delimiter closes outside
Error, Catch's comma/second-Pattern ordinal, an alternation Error before the
outer TypeAnnotation tail, and delegation to nested SymbolName/AliasBinding.
M1 pre-write and post-repair closure audits were clean. This is a
catalog-audited evidence-complete Draft only for the direct initial slots;
delimiter sequences/closes, defaults, other Pattern tails, nested grammar,
the global interpreter and ledger retirement remain separate.

#### PatternTypeAnnotation fresh required-Type Missing Draft links

Only fresh required-Type absence after direct Pattern annotation Colon is
linked. `Pattern > PatternTypeAnnotation > Colon TypeExpression(Missing)`
selects Pattern(TypeAnnotation); the TypeExpression and Missing are empty at
the direct post-Colon frontier. Nonempty Type(Primary) Error is separate.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/pattern/mod.rs:1106–1126,1384–1428` | `linked` | direct PatternTypeAnnotation/Colon shell, caller role and required-Type handoff |
| `crates/yu-syntax/src/type_expr/mod.rs:690–708` | `linked` | fresh required-Type Missing publication inside TypeExpression |
| `crates/yu-syntax/src/tests/pattern.rs:1907–1990` | `linked` | direct parentage/order/ranges, unique zero-width Missing, EOF and protected-newline handoff without records |

Nonempty Error/retry, accepted/nested Type, other boundary/origin/layout forms,
UTF-8/CRLF/Yumark, global interpretation and ledger retirement remain
untriaged, delegated or separately linked.

#### PatternTypeAnnotation required-Type primary Error Draft links

Only nonempty Type-primary Error after the Pattern annotation's direct Colon is
linked. `Pattern > PatternTypeAnnotation > Colon Native* Error+
TypeExpression?` selects Type(Primary); a following TypeExpression terminates
the adjacent Error group and owns retry leading. Fresh annotation absence is
Pattern(TypeAnnotation) and remains separate.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/pattern/mod.rs:1106–1126,1384–1428` | `linked` | direct PatternTypeAnnotation/Colon shell, required-Type delegation and boundary handoff |
| `crates/yu-syntax/src/type_expr/mod.rs:732–765` | `linked` | shared Type(Primary) Error publication and admitted Type retry |
| `crates/yu-syntax/src/tests/pattern.rs:1992–2081` | `linked` | direct order/ranges, terminal/retry, multi-leaf adjacency and protected-newline evidence without records or Error spelling |

Fresh Missing, accepted-only/nested Type, other caller and boundary forms,
UTF-8/CRLF/Yumark, global interpretation and ledger retirement remain
untriaged, delegated or separately linked.

#### RecordPattern item-phase structured Invalid row links

Only the following direct RecordPattern sites are linked to the bounded Draft
catalog row `(RecordPattern, item phase wrong-kind Pattern, RecordPattern
sequence context)`. They establish the direct Invalid-versus-separator-wrapper
topology and its nested Pattern/handoff behavior. They do not assign preceding
raw Error, comma Missing, close recovery, accepted record fields/defaults or
nested Pattern schemas.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/pattern/delimited.rs:297` | `linked` | after close/comma priority, record item-phase role selection chooses `RecordItem` only for a non-name/non-spread Pattern NUD |
| `crates/yu-syntax/src/pattern/delimited.rs:310` | `linked` | direct RecordPattern structured-recovery dispatch and caller-context forwarding |
| `crates/yu-syntax/src/pattern/delimited.rs:477` | `linked` | item role selects singleton Identifier and does not open the separator wrapper |
| `crates/yu-syntax/src/pattern/delimited.rs:500` | `linked` | existing structured Invalid emission retains the complete nested Pattern |
| `crates/yu-syntax/src/pattern/delimited.rs:513` | `linked` | nested Pattern entry retains stops, boundary and source ownership |
| `crates/yu-syntax/src/pattern/delimited.rs:972` | `linked` | record name/spread item-start discriminator that excludes accepted field/spread entries |

Focused direct Rowan proof is
`crates/yu-syntax/src/tests/pattern/recovery/sequence.rs:239–364, 408–458,
460–529, 624–695, 697–795, 859–961, 964–1052`. Every other Pattern row remains
untriaged, delegated, or unmapped unless separately linked below.

#### RecordPattern foreign-close raw Error row links

Only the consumed foreign-close path is linked to the bounded Authoritative
catalog row `(RecordPattern, one consumed foreign close, RecordPattern sequence
context)`. It adds `RecordPatternForeignClose(Error+)` without assigning direct
lexical Item/Separator Error groups, Missing, accepted fields, local/caller
close or nested Pattern schemas.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/pattern/delimited.rs:274` | `linked` | local/caller-close priority occurs before the foreign-close path and retains owner phase |
| `crates/yu-syntax/src/pattern/delimited.rs:553` | `linked` | only Record-owned `emit_wrong_close` opens/closes the wrapper around unchanged raw Error emission |
| `crates/yu-syntax/src/cursor/recovery/emit.rs:278` | `linked` | existing one-Item Error emission retains physical fragments and temporary record facts |
| `crates/yu-syntax/src/syntax_kind.rs:280` | `linked` | append-only public Rowan kind is `RecordPatternForeignClose = 275` |

Focused direct Rowan proof is
`crates/yu-syntax/src/tests/pattern/recovery/sequence.rs:5–202, 239–364,
798–856, 859–1052`. Ordinary direct Item/Separator Error groups and every
other Pattern row remain untriaged, delegated, or unmapped unless separately
linked below.

#### RecordPattern separator-phase structured Invalid row link

Only the existing structured-recovery emission at
`crates/yu-syntax/src/pattern/delimited.rs:500`, in its
`RecordPatternSeparator` separator-phase context, is linked to the referenced
catalog row `(RecordPattern, separator phase, RecordPattern sequence context)`.
Status: `linked`; linked fact: separator-phase `Invalid(Pattern(...))` is
wrapped by the authorized discriminator. Non-census implementation behavior is
support only. The direct item-phase Invalid and bounded foreign-close raw Error
are linked separately above; direct lexical Item/Separator Error groups and
every other Pattern emission remain unmapped.

### Literal and rule — 3 files / 6 calls

#### RuleLiteral indirect Missing publishers

The four semantic slots behind five `literal/rule_literal.rs` publishers are
now linked to direct Rowan proof in
`tests/literal/rule_literal.rs:rule_literal_child_slots_are_directly_distinguished_by_rowan_context`
and `interpolation_rule_sequence_error_group_is_direct_and_maximal`: two
interpolation-close exits share one `RuleLiteralInterpolation` Close slot;
braced lazy Close, unbraced lazy Name and outer terminator remain distinct.
Interpolation RuleSequence Error grouping uses its direct parent/context, never
temporary record count or Error spelling. Status: `evidence-complete Draft`
for those slots only; nested Rule children, global collector and ledger/API
migration remain open.

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

#### StringEscape and StringInterpolation brace row links

Only the following literal sites are linked to the bounded catalog row
`(StringEscape simple/Unicode slot or StringInterpolation brace slot, direct
StringLiteral piece context)`. They do not map StringPiece scanning,
InterpolationBody, the StringLiteral terminator or caller-owned boundaries.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/literal/mod.rs:420–490` | `linked` | optional/fragmented interpolation format, open Missing, Body delegation, accepted-close leading before close token, and boundary close-Missing order |
| `crates/yu-syntax/src/literal/mod.rs:627–656` | `linked` | direct simple-target token versus Missing after StringEscapeLead |
| `crates/yu-syntax/src/literal/mod.rs:671–794` | `linked` | ordered Unicode hex Error/Missing and final Unicode-end token/Missing paths |
| `crates/yu-syntax/src/literal/mod.rs:805–816` | `linked` | five existing LiteralRole-to-expected mappings |

Direct Rowan and fresh/frozen/shifted evidence is
`crates/yu-syntax/src/tests/literal.rs:819–1063, 1094–1200, 1387–1396` and
`crates/yu-syntax/src/tests/string_literal_recovery.rs:450–503, 570–620`.
Every other StringPiece/interpolation/literal row remains untriaged, delegated
or unmapped.

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

#### Rule ExpressionList caller-specific row links

Only the following direct caller/owner sites are linked to the bounded Draft
catalog row for RuleItem bracket, RuleCall and RuleIndex Item/Separator/Close
phases. The direct-caller fence tree/range proof remains open; this does not
classify a parser record or invent a fence CST slot.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/rule/expression_list.rs:54–157` | `linked` | Item/Separator phase selection, direct Error/Missing/Expression/Comma alternatives and unchanged boundary handoff |
| `crates/yu-syntax/src/rule/expression_list.rs:196–223` | `linked` | newline callback emits Item Missing before direct LF/CRLF Newline |
| `crates/yu-syntax/src/rule/mod.rs:513–538, 590–635` | `linked` | bracket RuleItem, RuleCall and RuleIndex delimiter/close ownership |

Direct Rowan proof is
`crates/yu-syntax/src/tests/rule_expression_list_recovery.rs:139–209, 624–839,
895–932`; its direct-caller fence limitation is `:842–893`. Every other Rule
and ExpressionList-related row remains untriaged, delegated or unmapped.

### Root, statement, and virtual layout — 3 files / 11 calls

- `crates/yu-syntax/src/root_statement.rs`
- `crates/yu-syntax/src/statement.rs`
- `crates/yu-syntax/src/virtual_statement_block.rs`

`rule/expression_list.rs` contributes two census calls and the separate
newline-Missing `exception` above. Its placement in this source-navigation
group does not classify that record-producing callback as a root/layout CST
slot.

#### Root direct raw Error ordered-context matrix

The independently audited candidate evidence links
`crates/yu-syntax/src/tests/root.rs:9–38,218–246,427–466,587–1190` to direct
Root publishers `crates/yu-syntax/src/root_statement.rs:174,261,338,431–552`.
It proves complete direct node/token ordering for Starter, Separator, 13
trailing statement owners and OperatorDefinitionBody, plus native semicolon/
CRLF grouping, UTF-8 opaque fragments, actual Equals and body Missing order.
This closes the former projection that discarded native tokens. Full Root
phase/terminal/fence coverage and nested owner schemas remain open.

#### Root direct raw Error bounded candidate links

Only `crates/yu-syntax/src/root_statement.rs:174,261,316–332,338,431–552` is linked to
the bounded Root raw-error candidate: root-entry phase selection, direct raw
Error emission, actual-Equals body dispatch and direct body Missing. Direct
proof is `crates/yu-syntax/src/tests/root.rs:9–38,218–246,427–466,587–1190`; test-only
cell-boundary support is `root_statement.rs:853–951`. Ordinary Root Missing,
nested statement/header recovery, outer Yumark and full Root grammar remain
separate rows.

#### BracedStatementBlock direct Missing ordered-context links

The bounded row links only the three direct Missing phases of
`BracedStatementBlockExpression`. Direct evidence at
`crates/yu-syntax/src/tests/braced_statement_recovery.rs:137–278` retains every
direct node/token and proves `Missing → BlockStatementSeparator` as required
Statement, `Statement → Missing → Statement` as missing Separator, and terminal
Missing as local Close. Nested-for evidence at `:499–606` keeps the accepted
outer RBrace terminal and applies the same separator rule after child
continuation. This invalidates the historical ancestry-only topology premise;
the proposed `BracedStatementBlockClose` and Separator wrapper are not
implemented. Braced Error/boundary variants, other Statement/layout owners,
the interpreter and ledger retirement remain separate.

#### StringInterpolationBody root-style statement-sequence row links

Only the following `virtual_statement_block.rs` sites, in the direct
`StringInterpolationBody` caller context, are linked to the mapped Draft row
`(StringInterpolationBody, repeated root-style Statement sequence, direct
child of an accepted StringInterpolation open brace)`. They establish only
the three cataloged recovery roles: `Statement(Missing)`/Starter, direct body
`Missing`/Separator, and direct body `Error+`/Starter. They do not assign a
schema to nested Statements, another block owner, the interpolation close, or
the literal terminator.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/virtual_statement_block.rs:67` | `linked` | root-style sequence entry; boundary and borrowed-`}` handoff precede sequence classification |
| `crates/yu-syntax/src/virtual_statement_block.rs:225` | `linked` | maximal direct body Error-run and admitted-Statement retry |
| `crates/yu-syntax/src/virtual_statement_block.rs:298` | `linked` | Error-run stop/boundary priority, including separator/newline/borrowed-close preservation |
| `crates/yu-syntax/src/virtual_statement_block.rs:309` | `linked` | explicit separator direct node and eligible successor-leading absorption |
| `crates/yu-syntax/src/virtual_statement_block.rs:347` | `linked` | newline separator direct node and successor-leading ownership |
| `crates/yu-syntax/src/virtual_statement_block.rs:354` | `linked` | required `Statement(Missing)` starter after leading/repeated explicit separator |
| `crates/yu-syntax/src/virtual_statement_block.rs:368` | `linked` | direct Missing/Error recovery role, expected syntax, range, and primary-alternative projection facts |
| `crates/yu-syntax/src/literal/mod.rs:460` | `linked` | direct `StringInterpolationBody` wrapper; enclosing interpolation retains close/Missing ownership |

Focused direct CST proof is
`crates/yu-syntax/src/tests/virtual_statement_block.rs:617–873`. Every other
root, statement, virtual-layout, literal, and Rule evidence site remains
untriaged, delegated, or unmapped unless separately linked above.

#### ProjectionRecordSpreadItem required-RHS row links

Only the following direct record-projection sites are linked to the bounded
Draft catalog row `(ProjectionRecordSpreadItem, required RHS immediately after
direct DotDot, direct ProjectionRecordTail spread-item context)`. They
establish the dedicated wrapper, direct marker, Missing/Error/retry alternatives
and handoff; they do not assign ordinary ProjectionRecord Item/Separator/Close
slots or the nested `OperatorChain` schema.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/delimited.rs:396` | `linked` | opens `ProjectionRecordSpreadItem`, emits direct `DotDot`, classifies its RHS and closes the wrapper before returning its exit |
| `crates/yu-syntax/src/expression/delimited.rs:425` | `linked` | initial malformed leading and maximal direct RHS Error-run entry |
| `crates/yu-syntax/src/expression/delimited.rs:440` | `linked` | admitted/retried RHS enters the nested `OperatorChain` path |
| `crates/yu-syntax/src/expression/delimited.rs:456` | `linked` | direct Missing only when Error has not already represented the failed RHS, followed by unchanged handoff |
| `crates/yu-syntax/src/expression/delimited.rs:476` | `linked` | phase-specific Missing boundary/ordinary-EOF leading publication |
| `crates/yu-syntax/src/expression/delimited.rs:519` | `linked` | lexical Error-run and its exact spread-marker/boundary stop conditions |

Focused direct Rowan proof is
`crates/yu-syntax/src/tests/owners.rs:553–906`; exact retained-role controls
are `crates/yu-syntax/src/tests/delimited_recovery.rs:304–335, 517–555`.
Every other delimited owner/phase remains untriaged, delegated, or unmapped.

#### Expression-delimited raw Item/Separator/foreign-close row links

Only the following expression-delimited sites are linked to the bounded
Authoritative catalog row `(one of five expression-delimited owners, raw Item /
raw Separator / one consumed foreign close, direct delimited-sequence context)`.
They do not assign accepted children, Missing, matching/protected close, fence,
or ProjectionRecord spread-RHS schemas.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/delimited.rs:154–173` | `linked` | inherited-close priority precedes one ForeignClose wrapper around exactly one existing foreign-close Error emission |
| `crates/yu-syntax/src/expression/delimited.rs:180–198` | `linked` | Parenthesized rejected semicolon is a Separator wrapper before unchanged Item-phase reset |
| `crates/yu-syntax/src/expression/delimited.rs:229–258` | `linked` | only Separator-phase lexical Error run is wrapped after initial leading; Item run remains direct and the existing Recovered transition remains intact |
| `crates/yu-syntax/src/expression/tails/delimited_tail.rs:36–79` | `linked` | the shared sequence is called only by Call, Index, ProjectionTuple and ProjectionRecord tails in addition to Parenthesized |
| `crates/yu-syntax/src/syntax_kind.rs:281–282, 500–504` | `linked` | append-only Rowan kinds and raw conversion are `ExpressionDelimitedSeparator = 276` and `ExpressionDelimitedForeignClose = 277` |

Focused direct Rowan proof is
`crates/yu-syntax/src/tests/delimited_recovery.rs:433–1258`; it covers the
five-owner Item/Separator/foreign-close matrix, mixed/repeated phases,
semicolon, comments, UTF-8, LF/CRLF, quote prefixes, protected closes/fence,
accepted controls and direct ProjectionRecord spread RHS. Every other
expression-delimited row remains untriaged, delegated, or unmapped.

#### Parenthesized/EffectRow Item, Separator and Close row links

Only the following shared Type-delimited sites are linked to the bounded Draft
catalog row `(ParenthesizedTypeGroup or EffectRowType, ordered
Item/Separator/Close phase, immediate P/E owner)`. They do not assign Call,
BracketRow, another Type owner, the global interpreter or API migration.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/type_expr/delimited.rs:50–204` | `linked` | shared P/E sequence entry, boundary/local-close priority and one `TypeDelimitedForeignClose` around each existing locally consumed mismatched-close Error |
| `crates/yu-syntax/src/type_expr/delimited.rs:650–745` | `linked` | non-Call Item Error run, exact stop set and direct Error-to-retry handoff; P/E Item groups remain unwrapped |
| `crates/yu-syntax/src/type_expr/delimited.rs:747–812` | `linked` | shared post-Error continuation, retry-leading ownership and protected/matching/EOF close disposition |
| `crates/yu-syntax/src/type_expr/delimited.rs:1284–1324` | `linked` | owner-selected Item and inherited Separator Missing publication |
| `crates/yu-syntax/src/type_expr/delimited.rs:1355–1425` | `linked` | owner-selected terminal Close Missing and parent-selected close expectation |
| `crates/yu-syntax/src/syntax_kind.rs:288,527–529,785,803` | `linked` | append-only `TypeDelimitedForeignClose = 283`, raw conversion and round-trip evidence |

Focused direct Rowan and retained continuation/record proof is
`crates/yu-syntax/src/tests/type_expr/pe_recovery.rs:97–594`. It covers P/E
collision pairs, Item/Close mixtures, separated and contiguous repeated
closes, exact wrapper contents/ranges, retry trivia, UTF-8, shifted/frozen
state, EOF, caller/fence/nested/PV paths and accepted/malformed Call and
BracketRow exclusions. Every other Type row remains untriaged, delegated or
unmapped unless separately linked above.

#### If arm BodyIntroducer, Body, ElseBody and IndentedStatement row links

Only the following sites are linked to the bounded Draft If-arm row. Condition
recovery remains delegated to the required-expression row; nested expressions,
statements, outer tails and other transported indented callers retain their own
schemas.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/if_expr.rs:200–344` | `linked` | If/Elsif arm, required Condition, no-cascade rule, actual-Colon Body selection and direct BodyIntroducer Missing |
| `crates/yu-syntax/src/expression/if_expr.rs:347–424` | `linked` | ElseArm ancestry and bare/colon ElseBody selection |
| `crates/yu-syntax/src/expression/if_expr.rs:427–503` | `linked` | actual-Colon choice between inline Body/ElseBody and transported IndentedStatementBlock |
| `crates/yu-syntax/src/expression/if_expr.rs:506–676` | `linked` | inline Missing, maximal raw Error group, retry-leading/OperatorChain continuation and role-selected projection |
| `crates/yu-syntax/src/statement.rs:510–552,773–942` | `linked` | shared indented block construction and transported direct Statement Missing/Error/retry |

Focused Rowan-only proof is
`crates/yu-syntax/src/tests/if_expr.rs:76–249`. Its 19 witnesses cover initial
If, Elsif and Else, inline and indented slots, no-cascade, maximal Error/retry,
accepted controls, UTF-8/CRLF ranges and nested equal-offset occurrence order.
Every other If boundary/caller and shared Statement row remains untriaged,
delegated or unmapped unless separately linked above.

#### For Pattern, header, iterable and body row links

Only the following sites are linked to the bounded Draft For row. Accepted
child Pattern/Expression/Statement and braced-body internals retain their own
schemas; no global interpreter or API state is assigned here.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/for_decl.rs:180–371` | `linked` | initial Pattern wrapper, terminal no-cascade, exact InKw admission and direct InKeyword Missing before Iterable/body continuation |
| `crates/yu-syntax/src/expression/for_decl.rs:374–524` | `linked` | ForIterable wrapper, required OperatorChain recovery and ordered handoff to body phase |
| `crates/yu-syntax/src/expression/for_decl.rs:527–599,697–770` | `linked` | direct BodyIntroducer Missing/Error, lexical grouping, native starter retry and boundary handoff |
| `crates/yu-syntax/src/expression/for_decl.rs:603–694` | `linked` | Colon-selected shallow Body Missing, inline required OperatorChain or transported indented Statement block |
| `crates/yu-syntax/src/expression/for_decl.rs:822–873` | `linked` | role-selected Missing/expectation projection, including BodyIntroducer's ordered Colon/Brace alternatives |
| `crates/yu-syntax/src/expression/required_operand.rs:73–275` | `linked` | For Iterable/Body required-expression Missing/Error grouping and retry ownership |
| `crates/yu-syntax/src/pattern/mod.rs:415–620,1228–1276` | `linked` | caller-selected initial For Pattern Missing/Error and nested Pattern ownership |
| `crates/yu-syntax/src/statement.rs:510–552,842–940` | `linked` | transported For IndentedStatement direct Missing/Error/retry |

Focused Rowan-only proof is
`crates/yu-syntax/src/tests/for_statement.rs:3–227`; the 15 cases cover every
mapped owner shape, terminal no-cascade, multi-fragment Error grouping, retry
leading and accepted inline/indented controls. Existing `for_c13_` controls
cover 12 accepted/recovery invariants. Labels, annotated Pattern details,
braced internals, exhaustive boundaries and nested grammar remain untriaged,
delegated or unmapped unless separately linked above.

#### CaseLike family row links

Only the following sites are linked to the bounded Draft CaseLike row. Nested
Pattern, Expression and Statement recovery remains delegated to those child
owners; the one combined Arrow/Body Missing remains one Rowan occurrence.

| Source evidence | Status | Linked fact |
| --- | --- | --- |
| `crates/yu-syntax/src/expression/case_like.rs` | `linked` | Case/Catch wrappers, direct Block/Arm order, CaseLike-owned inline Body Error/retry, Arrow/Body union, Separator and Catch-close completion |
| `crates/yu-syntax/src/expression/required_operand.rs:73–275` | `linked` | Scrutinee and Guard required-expression Missing/Error grouping and retry |
| `crates/yu-syntax/src/pattern/mod.rs:415–620,1228–1276` | `linked` | caller-selected first Pattern/Handler Missing/Error/retry and nested Pattern ownership |
| `crates/yu-syntax/src/statement.rs:510–552,842–940` | `linked` | transported `ColonApplication(IndentedStatement)` direct Missing/Error/retry |

Focused Rowan-only proof is the three `case_schema_` tests in
`crates/yu-syntax/src/tests/case_like.rs`. They cover both families, all nine
CaseLike roles including both Block interpretations, the single combined
Arrow/Body Missing, Body/Separator and
nested/close equal-offset ordering, Catch's LBrace-selected close, transported
indented Missing/Error/retry, accepted controls and UTF-8/CRLF coordinates.
Every exhaustive boundary/layout alternative, nested child schema and the
global interpreter remains untriaged, delegated or unmapped unless separately
linked above.

## Boundaries

The manifest deliberately excludes `cursor/recovery` implementation sites and
`src/tests` from the census. It does not enumerate non-emitter recovery facts,
direct token construction, public syntax-reference pages, or legacy parser
diagnostic ledgers. A family row becomes useful schema evidence only after the
catalog's required facts and the governing authority have been attached.
