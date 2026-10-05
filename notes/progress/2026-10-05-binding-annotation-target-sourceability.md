# Annotation discriminator: bounded target sourceability

Date: 2026-10-05
Baseline: `3ddcfdc65eb5c119e74ba160e5f8e3505f1e95e0`
Branch: `research/simple-sub-intrusion`
Status: unreviewed research characterization; no implementation authority
Method: direct source/grammar/API correspondence, with a conditional static
derivation of target CST shape; no executable parser experiment
Exclusive output: this note

## Objective and bounded conclusion

Determine whether the selected discriminator
`A={foo?:string}`, `B={}`, `C={foo?:int}` has a current raw-source target
denotation, rather than only abstract concrete-endpoint notation.

The spellings are derivable as named-record **syntax**. In the current lexer,
`foo?` is one `Identifier`; the record parser retains that token as the field
name. Neither that observation nor parser acceptance establishes that its
semantic field name is `foo` with optional presence. The inspected governing
syntax sources expressly exclude field/type meaning, and the compatibility
record expressly leaves optional-Record grammar and acceptance open.
Consequently this inventory grounds a CST-shaped candidate for the witness,
but does not ground its optional-Record target denotation. The selected witness
remains an abstract endpoint discriminator for this gate.

The first missing bridge is a source type-denotation clause: which admitted
raw target denotes a Record with optional field `foo`, and which environment
maps its payload names to the selected `string` and `int` endpoints? This
precedes the approved annotation-boundary comparison rule. No inference that
the literal suffix `?` must supply that clause is made here.

## Authority and dependencies

- Syntax architecture: Authoritative named-record addendum at
  `notes/design/2026-08-20-yu-syntax-chasa-architecture.md:12871`, its surface
  grammar at `:12922`, plain-identifier field restriction at `:12969`, and
  empty-record admission at `:13081`; equality-declaration scope at `:19166`
  and `TD-G` at `:19290`; nominal scope at `:19681` and `TND-G` at `:19790`.
  These sections define recognition/CST and exclude alias/nominal semantics
  and HIR lowering. Later attachment addenda do not provide a field denotation.
- Compatibility decision: `notes/design/2026-10-03-concrete-compatibility-boundary.md`
  §1, especially `:17–39`: one endpoint-dependent inequality; independent
  concrete successes cannot be composed. Its concrete discriminator at
  `:626–645` is retained as supplied semantic evidence, without rerunning any
  Oracle. The successor-syntax qualification at `:877–881` and explicit
  unapproved grammar/acceptance boundary at `:1034–1037` govern sourceability.
  §5's presence/child table is a candidate, not an adopted source rule.
- Committed `source-annotation-boundaries/q1`, answer `d1`, integration
  `28dddc75f`: the approved answer and receipt select direct checking at each
  binding/argument/expression annotation boundary, export the target plus
  local realization evidence, preserve earlier evidence, and forbid an
  intermediate concrete adaptation without a source boundary. They do not
  choose optional-field syntax or payload-name denotation; they do not grant
  compiler implementation authority. Current answer/receipt match the pinned
  baseline; no pending question bundle was consumed.

The syntax-reference pages read are the English named-record and type-core
pages, and equality/nominal declaration pages. Their authority/scope sections
explicitly exclude type meaning, lowering, resolution or field semantics.
Operational rules read: research-lab, design-authority, git-concurrency and
question-board. Task/lab/index reads served only as locators and context;
concurrent changes to those shared records are not evidence for this result.

## Static derivation and exact premises

Hypotheses for the parsing characterization: enter a required ordinary type
slot at the target's opening brace, with no incoming owner stop that owns that
brace; use the pinned maximal-identifier scanner and named-record production.
The following is a code/grammar derivation, not an observed parser run.

1. `scan_identifier` (`lexical/lexer.rs:685–700`) consumes identifier-start,
   zero or more identifier-continuation characters, then at most one `?`/`!`
   suffix (`:887–888`). Its `source_identifier` counterpart (`:724–740`)
   confirms the same maximal spelling. Thus `foo?:string` begins with
   `Identifier("foo?")`, followed by literal colon and `Identifier("string")`.
   `foo?:int` differs only in the RHS identifier. Lowercase payload names
   are ordinary identifiers, without a builtin meaning supplied by this lexer.
2. `is_type_record_field_name` (`type_expr/mod.rs:2449–2451`) accepts exactly
   `TokenKind::Identifier`. `type_record_field_normalized`
   (`type_expr/record.rs:386–427`) emits the whole name token inside
   `TypeRecordField`, then delegates colon and RHS parsing. It neither splits
   the suffix nor emits an optional-presence node. The RHS delegates to the
   canonical type entry (`:850–907`); ordinary identifier primaries are emitted
   by `type_expr/mod.rs:875–891`.
3. The derived shapes, with the explicit close wrapper, are:

   ```text
   A: NamedRecordType { LBrace, TypeRecordField Identifier("foo?") : TypeExpression Identifier("string"), NamedRecordTypeClose(RBrace) }
   B: NamedRecordType { LBrace, NamedRecordTypeClose(RBrace) }
   C: NamedRecordType { LBrace, TypeRecordField Identifier("foo?") : TypeExpression Identifier("int"), NamedRecordTypeClose(RBrace) }
   ```

   Braces and colons above denote retained punctuation, not semantic fields.
   There is no derived presence flag. In particular, parsing `foo?` as one
   name does not prove that optional fields are forbidden: a later semantic
   owner could assign the suffix a meaning under a separately approved rule.
4. The supplied discriminator outcomes are `A <: B` success, `B <: C`
   success, and `A <: C` failure. They do not follow from the three CSTs above.
   Deriving them for raw source additionally requires the missing target
   denotations and their local resolver/realization clauses. The approved
   annotation-boundary rule explains how already-denoting targets are used;
   it cannot substitute for their denotation.

For a minimal alternative spelling check, `type A = {foo?:string}`,
`type B = {}`, and `type C = {foo?:int}` fit `TD-G`'s equality RHS grammar.
The current equality parser delegates its RHS to the same required type entry
(`declaration/type_decl.rs:447–505`). These declarations therefore wrap the
same syntactic candidates; the inspected equality authority explicitly
excludes alias meaning/resolution. Bare `type A` provides nominal syntax but
also excludes nominal identity/constructor semantics. Neither inspected
declaration form repairs the denotation premise.

## Production boundary, independently inspected

`yu-types` has one source file. Its public `Leaf`, positive/negative indexed
node enums, positive/negative value-view enums and finalizer constructors
(`lib.rs:22–40`, `:105–129`, `:585–630`, `:1802–1936`) support integer,
bottom/top as applicable, quantified/recursive references, Function,
union/intersection, and the current empty/bottom effect forms. No Record,
String, field-name or optional-presence constructor occurs in that public
inventory. This establishes a representation gap for the audited public
canonical boundary, not a theorem that every conceivable encoded denotation
is impossible or that future constructors are already authorized.

Production HIR provides `ResolvedExpr::{Lambda,Integer,Name,Error}`
(`module.rs:426–449`) and `HirItem::{Binding,Expression,Error}` (`:613–621`).
Root planning admits an OperatorChain or BindingStatement and reports
`UnsupportedItem` for other roots (`:1038–1060`), including TypeDeclaration.
`plain_binding_header` (`:1471–1516`) accepts only plain identifier patterns
and its one supported parameter shape, so an annotated header does not gain
target elaboration. Expression association recognizes TypeAnnotationTail as
an association barrier (`lib.rs:305–314`), while semantic simple-chain lowering
requires a childless integer/name atom (`module.rs:1418–1468`); an unsupported
root expression becomes `UnsupportedExpression` (`:1260–1272`). These facts
are later implementation gaps, not the first semantic bridge and not an
approved permanent rejection policy.

## Evidence quality, commands, coverage and limits

The evidence uses primary repository grammar and implementation directly; it
does not depend on the prior explorer's conclusion. Grammar and parser share
the same intended syntax contract, so their agreement is correspondence
evidence, not independent proof of source type semantics. There is no
reference oracle, supplied-transition checker, seed/range enumeration,
mutation testing or measured parser output in this lane.

Commands: bounded `rg --files`, `rg -n` and `sed -n`/`cat` reads;
`git rev-parse HEAD`, `git branch --show-current`, `git status --short`,
`git ls-tree <baseline> <explicit input paths>`, and
`git diff <baseline> -- <explicit input paths>`. The explicit dependency diff
was empty before writing. No code, tests, builds, formatting, Git mutations
or external lookups were run. An initial locator request included `spec/`,
which does not exist in this checkout; syntax-reference was then inspected.
Initial broad locator captures were truncated; conclusions use later bounded
reads, not a claimed complete reading of the large syntax design.

Coverage is the named-record target grammar/owners, the two declaration forms
needed to assess aliases, the entire public constructor/view inventory of
yu-types, and the named HIR admission paths. Omitted: global source encoding
enumeration, library/import/type-name environments, user-defined semantic
constructors, full Struct/Act/impl/cast denotations, alternate bracket-row
encodings, parser execution, solver/runtime realization, full source adequacy,
and annotation-bearing recursive groups. No conclusion of global source
nonexistence is warranted. Peak CPU/RAM and exact elapsed wall time were not
instrumented; shell reads were lightweight, with no Cargo or long-lived probe.

Failure/invalidation conditions: a changed lexer/record owner invalidates the
static CST derivation; an in-scope approved target-denotation rule assigning
optional presence/payload endpoints changes the first-gap conclusion; a
new public canonical Record/String representation changes the API inventory;
other spelling routes can establish sourceability only with their own
approved denotation bridge. A candidate interpretation alone does not do so.

Recommended next action: have the primary freeze the annotation theorem at
supplied semantic endpoints and isolate the optional-Record target-denotation
bridge as its prerequisite, before using A/B/C as a raw-source completeness
discriminator.

## Frozen input blobs and commit packet

All listed direct inputs matched the baseline at the pre-write comparison.

| Input | Baseline Git blob |
| --- | --- |
| syntax architecture | `81e5fefa637b66f80999a4e3e4a0c84edae39171` |
| concrete compatibility | `07e2c58a928540c730dd67e74f2e65161ea6a9b5` |
| q1/d1 approved answer | `1b87624d94d01aff386f31acb81cc40b2bb3b441` |
| q1/d1 receipt | `54f566a38c5d1314b800824959e081ff663e2310` |
| reference named-record page | `1d00e2c7f47487494cfb0976d1df98011572b3a0` |
| reference type-core page | `865ecb66d119458bbfc98b3ec12e9e48119fd1ac` |
| reference equality page | `6d6325b070506404e647e3dc037b6b9aeba77704` |
| reference nominal page | `0fd35d494731fa3b23da930b8e0c13ac229b2b42` |
| `crates/yu-syntax/src/lexical/lexer.rs` | `39bbb4530967aa5998fa87f0e5c6031b1d9140d7` |
| `crates/yu-syntax/src/type_expr/mod.rs` | `8d042baa5fc8b69008a36e007dfad2b51679a7e1` |
| `crates/yu-syntax/src/type_expr/record.rs` | `43b8e742eab56604030c44ecf4d5793c9f6d476e` |
| `crates/yu-syntax/src/declaration/type_decl.rs` | `b2e10f1d5c88155c8743d2e5dc7f751c2bca90dd` |
| `crates/yu-types/src/lib.rs` | `c3a4e95d199fba0784b7e6448b6bb37a1f2c7798` |
| `crates/yu-hir/src/lib.rs` | `0c5e1ac6c1acba5707b33911be82fe4a1d75caa0` |
| `crates/yu-hir/src/module.rs` | `668d1b6f82fb17a96178a2353543d288c32e2762` |

- Exact leased/changed path:
  `notes/progress/2026-10-05-binding-annotation-target-sourceability.md`.
- Baseline SHA: `3ddcfdc65eb5c119e74ba160e5f8e3505f1e95e0`.
- Changed direct dependency hashes: none observed before writing; the primary
  must recheck before integration if HEAD/dependencies move.
- Claim/review status: bounded source correspondence plus conditional static
  syntax derivation; unreviewed, research-only; no own independent review claim.
- Checks already run: scoped source reads, baseline input diff and blob inventory;
  no executable validation required or performed for this note-only lease.
- Proposed commit message:
  `research: bound annotation discriminator target sourceability`.
- Shared deltas left for primary/curator: link this note from the annotation
  source-adequacy gate; distinguish target syntax from target denotation;
  retain A/B/C as abstract supplied endpoints until that bridge is established.
  No task, theory, index, authority or question-board path was modified.
