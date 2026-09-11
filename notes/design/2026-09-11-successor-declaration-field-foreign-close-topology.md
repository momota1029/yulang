# Declaration field foreign-close CST topology

Status: Authoritative; construction complete

Date: 2026-09-11

Drafted-by: primary from the architect's reviewed declaration field-list proposal

Reviewed-by: compiler_referee and spec_auditor

Approved-by: user

Approved-at: 2026-09-11

Scope: one transparent Rowan node around the existing maximal foreign-close
Error run in the shared declaration field driver's Struct delimited `Recover`
route. This does not change accepted grammar, Missing placement, recovery
records, frozen reconciliation, continuation, Enum/Error `Borrow`, indented
Struct fields, diagnostic APIs, the global CST interpreter or ledger removal.

Governing authority: the user's explicit approval on 2026-09-11, the
Authoritative CST-derived-diagnostics amendment,
Error-token/Invalid-node topology addendum and declaration field-sequence
current-Item recovery contract. This record authorizes and records the bounded
construction gate below.

## Proven collision

Raw recovery deliberately erases the original token kind to an `Error` leaf.
Consequently the pre-construction Struct field-list CST could not distinguish
Separator Error from foreign-close Error without consulting Error spelling or
the parser recovery ledger.

These initial and post-field pairs have identical Rowan kind/range/node-token
projections when Error spelling is opaque:

| pair | identical current suffix | hidden semantic difference |
| --- | --- | --- |
| `struct S{x:T;}` / `struct S{x:T]}` | `Error RBrace` | Separator / Close |
| `struct S{x:T;` / `struct S{x:T]` | `Error Missing` | Separator / Close, then Close Missing |
| `struct S{x:T;;}` / `struct S{x:T;]}` | `Error Error RBrace` | one Separator run / adjacent Separator then Close runs |
| `struct S{;x:T}` / `struct S{]x:T}` | `Error StructField RBrace` | initial Separator / initial Close |

The original direct control was renamed after the approved topology change to
`tests/declaration/struct_decl.rs::struct_field_separator_and_close_errors_are_distinct_without_error_spelling`.
It retains nesting, kinds, ranges, native non-Error text and node/token identity
while masking only Error spelling. Temporary records prove the different roles
and one-run versus two-run partition; they are counterexample and preservation
evidence, never a future interpreter input.

The old topology violated the CST-derived amendment's unique-slot prerequisite.
The completed construction resolves this collision. The existing parser still
publishes records until the later atomic migration; this local repair alone
does not authorize ledger retirement.

## Implemented decision

Append one `SyntaxKind::StructFieldForeignClose` and emit:

```text
StructFieldForeignClose := Error+
```

The node is a direct child of the Struct declaration's named-brace or
tuple-parenthesis field-list sequence. Despite the established `StructField`
prefix in its name, it is never a child of one field. It identifies the
field-list foreign-close recovery occurrence.

Open exactly one wrapper immediately around the existing maximal Error-run
operation in `declaration::fields::recover_close_normalized`; finish it before
returning the retry or boundary Item to the sequence loop. One wrapper denotes
one recovery run, not one malformed token. Multiple foreign closes and internal
raw trivia consumed by that run remain adjacent `Error` children of the same
wrapper.

Only the Struct delimited `FieldOuterClose::Recover` route can emit the node.
Matching local close is consumed before this route. Enum/Error named and tuple
payloads use `Borrow` and remain unchanged; indented Struct fields have no local
delimited close recovery and remain unchanged.

## Rowan and diagnostic contract

After construction, the two field-list raw categories are structural:

```text
direct field-list Error+                 => FieldSeparator Error
StructFieldForeignClose(Error+)          => Struct closing-delimiter Error
```

The qualification "field-list" is mandatory. Error nested in `StructField`
remains Field/Name/Colon/Type-owned according to its own catalog rows.

`StructFieldForeignClose` has no diagnostic of its own. Its one maximal Error
group projects the opener-selected closing delimiter: brace for
`StructNamedFields`, parenthesis for `StructTupleFields`, primary alternative
zero, over the combined UTF-8 child range. Direct list Error retains
`Struct(FieldSeparator)` with `DelimitedSequenceSeparator`. Wrapper boundaries,
native trivia, Missing and nested nodes terminate Error grouping. Normal Rowan
preorder therefore preserves adjacent Separator then Close, or Close then
Separator, as two occurrences without reading Error text.

No `Invalid`, expectation payload, recovery ID, attribute, counter or parallel
state is added to the CST.

## Source, leading and handoff

Initial leading is emitted by the sequence before the wrapper opens. Internal
leading consumed by the existing raw run remains `Error` content inside the
wrapper. Retry and protected-boundary leading stays pending outside. The
wrapper finishes before an admitted field, comma, semicolon, matching close,
Close Missing, EOF completion or caller continuation.

The existing scanner, stop/retry predicates, maximal-run extent, role,
expectation, record cardinality/order, frozen replay, source bytes and Item
handoff remain unchanged. The change adds one malformed-run wrapper and no
additional source traversal.

Accepted comma/newline, matching close, every Missing and all accepted CST are
unchanged. Actual-close-only trailing attachment remains unchanged.

## Narrow supersession

On approval, this design supersedes only the Error/Invalid topology addendum's
direct-owner placement requirement for Error runs emitted by
`recover_close_normalized` on the Struct delimited `Recover` route. The Error
leaves remain physical raw fragments, now grouped by one transparent owner
node. All declaration field-sequence recovery semantics retain authority.

## Alternatives

`DeclarationFieldSeparator(Error+)` around every shared Separator run also
resolves the collision, but changes malformed ancestry across named/tuple,
Struct/Enum/Error and indented callers. It supplies no additional distinction,
so the narrower Struct foreign-close wrapper is selected.

Two wrappers are redundant. A terminal Close node containing accepted close or
Missing changes accepted CST and exceeds the collision. `Invalid`, synthetic
Missing, Error-spelling classification, retained parser provenance and reuse of
expression-specific delimiter nodes conflict with existing authority.

## Construction and verification gate

After user approval, use M2 with one implementation pass and at most one repair
bundle. Append the kind without renumbering existing values or filling the
intentional raw holes. Extend raw conversion and round-trip checks.

Focused direct Rowan evidence must cover:

- the four collision pairs above becoming structurally distinct while their
  source, records, ranges and continuation remain unchanged;
- named and tuple Struct lists; initial, post-comma and post-field positions;
- Separator-only, Close-only, Separator→Close and Close→Separator order;
- multiple foreign fragments in one wrapper and separate later runs;
- retry to field, comma, semicolon and matching close; EOF and active/fence
  handoff; initial/internal/retry trivia including UTF-8/CRLF;
- unchanged Enum/Error `Borrow`, indented Struct, nested field Type recovery,
  accepted lists, direct Missing and accepted punctuation.

Run the focused declaration/SyntaxKind/normalization controls, one package
check, format and scoped diff. Benchmark budget is zero unless implementation
exposes material uncertainty.

Stop and return to design if an accepted tree, record, range, leading owner,
continuation, wrapper-per-run cardinality or existing discriminant changes; if
another caller gains the node; or if any Separator/Close collision remains.

## Recorded approval

The user approved option B on 2026-09-11: append
`StructFieldForeignClose`, wrapping exactly one existing maximal Struct
delimited foreign-close Error run, with no diagnostic on the wrapper and
unchanged recovery, leading, records, Missing and accepted CST. The approval
includes the narrow topology supersession above and the corresponding
collision-test ancestry/equality updates.

## Completion

`StructFieldForeignClose` was appended as raw kind 278. The shared declaration
field driver opens exactly one wrapper around the unchanged maximal Struct
delimited foreign-close Error run and closes it before returning the retry or
boundary Item. No scanner, predicate, recovery record, Missing, accepted path,
Enum/Error Borrow path or indented Struct path changed.

Focused construction evidence covers the four former opaque-spelling
collisions, named and tuple positions, adjacent Separator/Close order,
multi-fragment and repeated runs, UTF-8/internal trivia, fresh/frozen equality,
active-stop and protected-fence leading, real indented fields, and sibling
exclusions. Declaration (294), SyntaxKind (3), normalized (83) and recovery
output (26) tests passed; `cargo check -p yu-syntax`, format and diff checks
passed. Independent specification review found one test-evidence gap; one
bounded repair added the real colon-introduced indented control and direct
fence witness, and delta review closed. Independent compiler/recovery review
was clean. Benchmark use was zero samples/processes.

The global CST diagnostic interpreter, FieldSeparator/Close catalog rows,
parser-ledger retirement, public API migration and workspace-wide final check
remain outside this completed gate.
