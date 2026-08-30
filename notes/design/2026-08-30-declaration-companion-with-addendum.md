# Declaration companion `with:` grammar addendum

Status: Authoritative

Scope: `Struct` / `Type` / `Enum` / `Error` / `Act` declaration-owned companion grammar,
lossless CST, parser AST, typed recovery, owner handoff, state restoration, and implementation gates.

Approved-by: user

Approved-at: 2026-08-30

Drafted-by: `architect` role, adjudicated and recorded by the primary agent

Reviewed-by: independent `compiler_referee`, `spec_auditor`, and `performance_auditor`

Supersedes: only the named deferred companion boundaries in
`2026-08-20-yu-syntax-chasa-architecture.md`; no implementation is authorized while this
document remains `Reviewed`.

Date: 2026-08-30

## 1. Purpose and authority

This addendum closes the declaration-owned `with:` / `with {}` grammar that the generic-expression
`WithBodyTail`, Struct, Derives, Act, Enum, Error, and Type-attached Impl addenda deliberately
deferred. It does not reinterpret the expression tail as a declaration companion.

The governing order remains:

1. a current explicit user decision;
2. this addendum after it becomes `Authoritative`;
3. the parent chasa architecture and its existing Authoritative addenda;
4. confirmed code and test invariants.

User approval makes this addendum authoritative within its declared scope. Deferred-scope tests
superseded by an implementation gate change only at that gate's atomic promotion point.

## 2. Selection and scope

The next parser slice is the shared declaration companion rather than `where`, doc-comment
declarations, Type role-like bodies, or the Cast malformed-delimiter residual.

The reasons are:

- `where` still lacks an owning declaration design, and the current authority forbids inventing a
  Type-specific clause;
- doc-comment declaration ownership is a separate statement-family decision;
- Type role-like bodies affect one owner, while companion seams already exist across five owners;
- the Cast residual is an accepted malformed-input family with higher recovery risk and no new
  valid surface.

Included:

- declaration owners `Struct`, `Type`, `Enum`, `Error`, and `Act`;
- exact contextual `with` followed by colon-inline, colon-indented, or braced companion bodies;
- ordinary canonical Statements and companion-only Derives runs as companion items;
- owner attachment priority and completeness;
- AST/direct-CST parity, typed recovery, losslessness, boundary ownership, and rollback-owned state;
- a statically specialized shared item-sequence skeleton with zero ordinary-path behavior change.

Excluded:

- generic-expression `WithBodyTail` changes or desugaring between expression and declaration forms;
- companions on `Role`, `Impl`, `Cast`, or `Mod`;
- Type colon/brace role-like bodies;
- standalone `derives` Statements;
- post-`AttachedImpl` companions;
- host Act, Impl-specific `via`, declaration `where`, doc-comment declarations;
- method attachment, receiver classification, generated impls, HIR, resolver, inference, formatter,
  or any companion semantics;
- attachment after an explicit declaration-terminating semicolon;
- attachment after indented declaration bodies or equals-indented variant bodies.

## 3. `DC-G`: canonical grammar

```text
DeclarationCompanion ::= DeclarationCompanionGap WithKw CompanionForm

CompanionForm ::= CompanionColonForm | CompanionBraceForm

CompanionColonForm ::=
    HorizontalTrivia RecoveredColon HorizontalTrivia RequiredCompanionItem OptionalTerminalSemicolon
  | HorizontalTrivia Colon StrictlyDeeperTrivia RequiredIndentedCompanionItems

RecoveredColon ::= Colon | Missing(Colon)

RequiredIndentedCompanionItems ::= CompanionItem CompanionSequenceTail*

CompanionBraceForm ::=
    HorizontalTrivia LeftBrace CompanionBraceItems RightBrace

CompanionBraceItems ::= empty | CompanionItem CompanionSequenceTail*

CompanionItem ::= CompanionDerivesRun | CanonicalStatement

CompanionDerivesRun ::= DerivesClause+
```

The colon form is non-empty. An inline colon body has exactly one companion item and may consume one
terminal semicolon. An indented colon body has one or more items. A braced body may be empty.

`CompanionSequenceTail` uses the existing canonical statement-sequence separator authority for the
selected layout: actual semicolon, accepted braced separator, or qualifying physical newline. It
does not invent a synthetic separator token. A missing separator between two recognizable items is
typed companion recovery.

One Derives run may contain repeated clauses without an intervening statement separator. Each
`DerivesClause` remains its existing AST/CST value and recovery owner. `derives` is tried before
Canonical Statement only inside a committed declaration companion item slot.

## 4. Declaration-companion gap

`DeclarationCompanionGap` is a new Y3 rule, not inherited from generic `WithBodyTail`.

An eligible owner position may reach exact `with` through:

- horizontal trivia on the same physical line; or
- a physical newline whose next token is strictly deeper than the declaration base.

Equal-or-shallower newline, a visible ambient owner boundary, active caller punctuation, or EOF wins
before the contextual word probe. Rejected trivia and `with` remain unconsumed.

Consequences:

- normal dedent after an indented declaration body does not open a companion attachment;
- Struct/Enum/Error colon-indented bodies and Enum/Error equals-indented bodies do not gain a
  trailing companion position;
- a recovered field/variant/item, missing close, mismatched close, or incomplete body does not open
  an attachment position;
- a completed braced/tuple/equals-inline position still requires the gap rule above;
- `withx` and `within` never prefix-split.

This deliberately favors statement-boundary ownership over the broader historical Y2 helper after
indented bodies.

## 5. `DC-J`: judge and priority

At an eligible owner position, judge order is:

1. actual local punctuation and matching-close authority;
2. active caller / ambient boundary;
3. qualifying declaration-companion gap;
4. exact maximal word `with`;
5. after commitment, actual `{`, then actual `:`, then missing-introducer recovery;
6. inside an item slot, exact companion `derives` run before Canonical Statement;
7. malformed item recovery only when no valid item candidate is present.

Exact `with` is positive evidence and commits `DeclarationCompanion` independently of introducer or
body success. Missing introducer recovery selects the colon form with an incomplete colon slot, so a
valid inline item at the same position is retained in the AST and CST.

Fresh-primary handoffs are fixed as follows:

| source state | result |
| --- | --- |
| `type T derives with:` | one Missing Derives RoleReference, then Type companion |
| `type T = with:` | one Missing Type RHS, then Type companion |
| `act with:` | one Missing Act Head, then Act companion; no Source/Body cascade |
| `act A = with:` | one Missing Act Source, then Act companion; no Body cascade |
| `enum E = with:` | one Missing Enum variant, then Enum companion |
| `enum E = A \| with:` | one Missing Enum variant after the pipe, then Enum companion |
| `enum E = A from with:` | one Missing FromType, then Enum companion |
| corresponding Error equals-inline rows | same local missing slot, exact `with` yielded to the outer Statement owner; no Error companion |

Nested TypeExpression episodes suspend the scoped `With` stop. Only the outer logical owner episode
may hand the exact word to a declaration companion or outer Statement.

## 6. Owner and attachment matrix

`Header derives` means the existing shared Header attachment run. `Trailing derives` retains DRV's
existing restriction: only the already-authorized actual-complete braced/tuple owners expose it.

| owner | accepted position and order | predecessor completeness | explicitly rejected positions |
| --- | --- | --- | --- |
| Type Header | Header derives -> AttachedImpl probe -> Companion -> Equality -> future role-like body -> Nominal/recovery | complete Name; parameters as currently accepted; a fresh missing Derives RoleRef may hand off | after AttachedImpl; after explicit semicolon; equal/shallow newline |
| Type Equality | mandatory RHS -> existing trailing derives -> Companion | RHS Complete or locally recovered to the scoped `With` owner tail; missing RHS has exactly one RHS recovery | after AttachedImpl; after owner boundary |
| Struct Header | Header derives -> Companion or Struct body | exact `with` is positive body evidence | bare EOF/boundary remains Missing BodyIntroducer; no implicit bodyless fallback |
| Struct trailing | actual-complete named-brace or tuple close -> existing trailing derives -> Companion | matching close must be actual | named-indent dedent; bodyless semicolon; missing/mismatched close |
| Enum Header | Header derives -> Companion or Enum body | exact `with` selects existing implicit bodyless form plus companion | explicit semicolon; rejected gap |
| Enum trailing brace | actual-complete brace -> existing trailing derives -> Companion | matching close actual | colon/equals-indented dedent; missing/mismatched close |
| Enum equals-inline | variant sequence -> Companion | at least one accepted or explicitly recovered mandatory variant slot; trailing pipe / FromType recovery may hand off once | equals-indented; after outer boundary |
| Error Header | Header derives -> Companion or Error body | exact `with` selects existing implicit bodyless form plus companion | explicit semicolon; rejected gap |
| Error trailing brace | actual-complete brace -> existing trailing derives -> Companion | matching close actual | colon/equals-indented dedent; missing/mismatched close |
| Error equals-inline | no companion; inline variant episode yields exact `with` to outer Statement | local missing Variant/FromType recovery may occur before yield | all Error equals-inline companion attachment |
| Act post-Head | Head -> Header derives -> Companion **or** Source/body decision | Head Complete, locally recovered, or Missing at exact `with`; one Head recovery maximum; accepted Companion terminates Act continuation | second companion, Source/body after a companion, post-body, explicit semicolon |
| Act post-Source | Source -> Header derives -> Companion **or** body decision | Source Complete, locally recovered, or Missing at exact `with`; one Source recovery maximum; accepted Companion terminates Act continuation | second companion, body after a companion, post-body, explicit semicolon |

Error equals-inline intentionally preserves the Y2 owner distinction: Enum retains the yielded `with`
as its companion, while Error returns it to the outer Statement owner. This is not described as
uniform Enum/Error behavior.

## 7. Explicit episode and owner-tail wiring

Implementation must not infer these handoffs from the outer attachment table.

### 7.1 Derives RoleReference episodes

All eligible Header/Trailing Derives owner specs add a depth-fenced `StopKind::With`. The stop is
visible only in the outer RoleReference episode. Nested parenthesized, call, forall, arrow,
polymorphic-variant, record, and row TypeExpression episodes suspend it.

`DerivesOwnerTail` gains a typed declaration-companion handoff carrying the declaration owner and
position. `type T derives with:` and sibling owner rows create one Missing RoleReference and leave
`with` unconsumed for the companion adapter.

### 7.2 Act Head and Source

Both Act TypeExpression episode specs add outer-only `StopKind::With`, ordered with existing
Derives/Equals/body punctuation rules. Fresh primary treats exact `with` as owner tail, not a valid
Head or Source primary. Nested episodes suspend it.

Act owns at most one companion. Selecting the post-Head companion ends the Act before Source/body
classification; selecting the post-Source companion ends it before body classification. Bytes after
the completed companion are returned to the outer Statement owner. In particular,
`act A with {} = B with {}` contains one Act companion; the first `=` and everything after it are
outside that Act. This preserves the singular AST/CST field and the Y2 terminating-companion path.

### 7.3 Enum/Error equals-inline payloads

The shared variant driver receives an owner spec that makes outer equals-inline FromType and
PositionalPayload episodes yield exact `with`. Nested TypeExpression episodes suspend the stop.

- Enum maps the yield to its companion continuation.
- Error maps the same yield to its outer Statement continuation and never opens an Error companion.

The shared driver does not decide attachment ownership by itself.

### 7.4 Type Equality RHS

The existing scoped `StopKind::With` behavior is retained and made an explicit Type companion tail.
Nested TypeExpression episodes continue to suspend it. Missing/malformed RHS recovery hands off only
under the existing mandatory-slot no-cascade rules.

No global `StopKind::With` activation is permitted.

## 8. `DC-T`: AST and CST contract

### 8.1 AST

```rust
struct DeclarationCompanion<'source> {
    keyword: Range<usize>,
    form: DeclarationCompanionForm<'source>,
    range: Range<usize>,
}

enum DeclarationCompanionForm<'source> {
    Colon {
        colon: Recovered<Range<usize>>,
        body: Recovered<DeclarationCompanionColonBody<'source>>,
    },
    Braced {
        open: Range<usize>,
        items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
        close: Recovered<Range<usize>>,
    },
}

enum DeclarationCompanionColonBody<'source> {
    Inline {
        item: Box<DeclarationCompanionItem<'source>>,
        semicolon: Option<Range<usize>>,
    },
    Indented(DeclarationCompanionIndentedBody<'source>),
}

struct DeclarationCompanionIndentedBody<'source> {
    base_indent: usize,
    block_indent: usize,
    items: Vec<Recovered<DeclarationCompanionItem<'source>>>,
    range: Range<usize>,
}

enum DeclarationCompanionItem<'source> {
    Statement(Box<Statement<'source>>),
    Derives(Vec<DerivesClause<'source>>),
}
```

Each of the five declaration ASTs gains `companion: Option<DeclarationCompanion>`.

The field is singular for every owner. For Act, the terminating rule in §7.2 prevents both the
post-Head and post-Source positions from being selected in one declaration.

Struct additionally gains:

```rust
StructBody::CompanionIntroduced
```

This variant may be constructed only after exact companion `with` evidence is accepted at the
Struct Header position. Existing `StructBody::Bodyless { semicolon }` remains literal-semicolon only.
`struct S` at EOF/boundary remains `Recovered::Incomplete` with the existing BodyIntroducer
recovery. `struct S with ...` has `CompanionIntroduced` even when the committed companion later
recovers a missing introducer/body.

### 8.2 CST

Add exactly:

- `SyntaxKind::DeclarationCompanion`;
- `SyntaxKind::DeclarationCompanionIndentedBody`.

The declaration owner contains one `DeclarationCompanion` child. The companion contains `WithKw`,
actual/missing introducer output, and then:

- inline: one direct `Statement` or one-or-more direct `DerivesClause` children;
- indented: one `DeclarationCompanionIndentedBody` containing direct item children;
- braced: actual braces and direct item children.

`DerivesClause` is never wrapped in `Statement`. No generic `WithBodyTail`,
`IndentedStatementBlock`, or `BracedStatementBlockExpression` node is reused. Missing/Error nodes
follow the existing one-record/one-node contract and source order.

## 9. Static sequence architecture and performance contract

The existing canonical statement sequences are hot paths. They must not gain a runtime companion
mode, a per-item `if companion`, a trait object, a closure dispatch, or an ordinary-path `derives`
probe.

The allowed shared shape is a zero-sized, statically dispatched owner/item spec, monomorphized
separately for ordinary Statement and declaration companion sequences. An equivalent duplicated
thin loop is allowed if static specialization cannot preserve generated ordinary behavior.

The spec must supply:

- candidate recognition;
- AST item parse and result type;
- direct-CST streaming commit;
- item wrapper policy;
- Missing/Error item role;
- separator role and missing-separator recovery;
- close owner;
- empty/non-empty cardinality;
- terminal boundary and owner stop.

AST and direct paths use separate thin adapters over the same sink-free decisions. AST allocates
only its one result `Vec<Recovered<DeclarationCompanionItem>>`. Direct CST streams once and never
builds/replays that Vec. No clone, side index, second vector, cache, post-parse classification, or
CST rescan is allowed.

Ordinary Statement specialization must call exactly the current canonical candidate/parse/commit
and recovery functions. Root parsing is outside this extraction.

Implementation rollback condition: any new ordinary item-level dynamic branch/probe, rescan,
allocation, range change, recovery change, or measurable time/RSS regression outside repeated-run
noise.

## 10. `DC-R`: typed recovery and owner convergence

Add:

```rust
enum DeclarationCompanionRole {
    Introducer,
    Body,
    Item,
    IndentedItem,
    Separator,
}

DeclarationRole::Companion(DeclarationCompanionRole)
ConstructRole::DeclarationCompanion
```

Brace closing recovery uses
`GrammarRole::ClosingDelimiter { owner: ConstructRole::DeclarationCompanion, delimiter: Brace }`.
It never uses `BracedStatementBlockExpression` identity.

| input/state | recovery | continuation/ownership |
| --- | --- | --- |
| `with` + EOF/owner boundary | one zero-width Missing Introducer; Colon form, colon/body Incomplete | no Body cascade; boundary non-consume |
| `with item` | one Missing Introducer; Colon form with body Complete Inline | retry item at same position; preserve item |
| `with :: item` | one maximal Error Introducer over malformed punctuation | retry actual colon/brace or valid inline item; no added Missing |
| `with:` + complete inline item | zero companion recovery | optional one terminal semicolon may be consumed |
| `with:` + EOF/equal-shallow newline/wrong indent | one Missing Body | gap/boundary non-consume |
| `with:` + deeper trivia + zero items | one Missing Body | indented body Incomplete; no Item cascade |
| `with {}` | valid empty Braced form | zero item/recovery |
| brace leading/repeated accepted separator | one Missing Item per committed empty slot | separator actual; next slot retry |
| brace trailing accepted separator before `}` | valid trailing separator only where ordinary braced sequence already permits it | no empty item |
| two recognizable items without separator | one zero-width Missing Separator | second item retry at same position |
| malformed item + valid item | one maximal non-empty Error Item | valid item retry; no Missing |
| malformed item reaches close/boundary | one Error Item, item Incomplete | close/boundary non-consume; no added Missing |
| companion Derives malformed internals | existing DerivesRole recovery only | companion adds no duplicate Item recovery |
| brace EOF | one Missing companion-owned ClosingDelimiter | no Body/Item cascade |
| mismatched local close | one companion-owned Error ClosingDelimiter | local mismatch handled once |
| outer-owned close/comma/semicolon/If companion/dedent | no consumption by companion item scanner | active owner receives same byte |
| missing Struct/Type/Act/variant predecessor slot at exact `with` | predecessor's one Missing/Error as fixed in DC-J | companion recovery begins only after handoff; no same-cause cascade |

One source range has one recovery owner. Inner Canonical Statement and Derives recovery wins over
outer companion recovery for bytes already claimed by that inner construct.

## 11. State restoration

Normal, Missing, Error, retry, rejection rollback, empty brace, missing/mismatched close, and nested
Statement exits must restore exactly:

- input and line state;
- sink/node balance and diagnostics checkpoint;
- inline / ML / type-ML modes;
- delimiter and stop stacks;
- indentation baselines;
- ambient owner and If companion scopes;
- TypeExpression episode depth/scoped stop frames;
- TypeDelimited owner state;
- positional fence state.

The companion brace owns its own ambient barrier and delimiter. The companion indented body owns a
companion-specific indentation/block scope. Neither mutates the generic `WithBodyTail` owner roles.

## 12. Named Y2/Y3 distinctions

1. Y2 used a separate companion statement dispatcher; Y3 preserves that conceptual separation but
   uses typed AST/direct adapters and recovery.
2. Enum equals-inline retains `with` as a companion. Error equals-inline yields the same spelling to
   the outer Statement and does not attach it.
3. Equal/shallow newline never opens a companion; indented declaration bodies have no trailing
   companion position in this slice.
4. Struct Header companion is a new explicit valid body form, not a general implicit-bodyless Struct.
5. `WithKw` is contextual at owner attachment positions; source-wide keywording is forbidden.
6. Companion derives is a direct companion item, never a standalone Statement.
7. Parser recovery identity and source order are not normalized into semantic method/derive plans.

## 13. Implementation gates

User approval has recorded this document as `Authoritative`. Implementation begins at Gate 1 and
must follow the gate order below.

1. **Vocabulary scaffold.** Add the two SyntaxKinds, companion AST/role/ConstructRole vocabulary,
   owner fields, and unreachable `StructBody::CompanionIntroduced`. No production reachability or
   behavior change.
2. **Static sequence core.** Extract the zero-sized statically specialized AST/direct sequence
   skeleton. Ordinary Statement paths and all existing range/recovery fixtures remain byte-identical.
   Run performance inspection and baseline measurements before continuing.
3. **Isolated companion form.** Implement exact `with`, colon/brace forms, dedicated item values,
   separator/close ownership, DC-R, and full rollback matrix in an isolated harness.
4. **Companion Derives item.** Reuse the existing DerivesClause driver with companion-only item
   priority; standalone Statement grammar remains unchanged.
5. **Typed episode handoffs.** Add Derives owner tails, Act Head/Source scoped stops, Type Equality
   tail, and owner-parameterized Enum/Error equals-inline yields. No owner adapter is production yet.
6. **Type owner.** Wire Header and Equality positions, preserve AttachedImpl priority, and close
   missing RHS/Derives handoff rows.
7. **Struct owner.** Wire Header `CompanionIntroduced` and actual-complete brace/tuple trailing
   positions. Preserve bare Struct and missing-close behavior.
8. **Enum/Error owners.** Wire shared Header/actual-brace positions, Enum equals-inline companion,
   and Error equals-inline outer yield. Preserve their intentional difference.
9. **Act owner.** Wire post-Head/post-Source positions and derives order; post-body remains rejected.
   Either accepted companion terminates Act continuation. Fix post-Head-only, post-Source-only, and
   `act A with {} = B with {}` one-companion AST/direct-CST fixtures.
10. **Atomic public/final scope gate.** Exercise all owner/position rows through public AST and
    direct-CST entrypoints, generic-With negatives, contextual word negatives, workspace scope audit,
    and state/performance matrices.

Each grammar/recovery/CST/AST gate requires independent `compiler_referee`, `spec_auditor`, and
`regression_auditor` review. Gate 2 and any later loop/allocation change also require
`performance_auditor` review.

## 14. Verification and rollback gates

Per-gate focused fixtures precede `cargo test -p yu-syntax`. Final verification may add the safe
workspace checks governed by `rules/testing.md` after focused resource behavior is understood.

Performance evidence for Gate 2 uses fixed 1k and 10k ordinary indented/braced blocks and a
companion-heavy case, repeated with `/usr/bin/time -v` (or a later approved equivalent). Record wall
time and peak RSS. Any ordinary-path regression outside measured noise or any static inspection
failure rolls the extraction back.

Re-enter architecture rather than patch locally if implementation requires:

- `Statement::Derives`;
- global `StopKind::With`;
- AST/direct judge duplication;
- attachment across a missing/recovered close or equal/shallow boundary;
- generic `WithBodyTail` behavior changes;
- dynamic ordinary item dispatch, rescanning, replay, or extra allocation;
- a new owner position absent from the closed matrix.

## 15. Approval decision

The recommended approval unit is this one shared addendum for all five declaration owners, with
separately rollbackable owner gates. Approving only the common core plus Type/Struct would leave the
shared episode and Enum/Error/Act ordering decisions unresolved and require another design cycle.

User approval on 2026-08-30 changed this document's status to `Authoritative`; Gate 1 is the active
implementation step.
