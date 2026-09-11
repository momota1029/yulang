# NamedRecordType recovery-slot CST draft

Status: Authoritative; private M2 construction complete

Date: 2026-09-10

Approved-by: user

Approved-at: 2026-09-11

Drafted-by: primary from the NamedRecordType collision investigation

Scope: a proposed CST topology distinction for the existing
`NamedRecordType` sequence only. It covers direct whole-Field recovery,
separator recovery and final close ownership. It does not change accepted type
grammar, current-Item scanning, field Name/Colon/RHS ownership, operator/type
tail selection, Error/Invalid meaning, parser records, frozen reconciliation,
public diagnostics, API migration or recovery-ledger retirement.

Governing authority: the Authoritative CST-derived diagnostics amendment,
Error/Invalid topology-ordering addendum, record sequence current-Item recovery
and record field current-Item recovery. The user's 2026-09-11 approval adopts
the topology below as the construction authority.

## Proven collision

The existing direct Rowan test with `{([)]:A}` retains two temporary Error
records:

```text
Type(RecordField), Identifier,       1..3   // "(["
Close(NamedRecordType, Brace), `}`,  3..7   // ")]:A"
```

Yet its lossless CST has one immediate `NamedRecordType` run of six adjacent
`Error` tokens over `1..7`, with no `TypeRecordField`, `Missing` or other node
between the Field and Close portions. The existing raw-group utility expressly
coalesces adjacent Error leaves of one immediate parent across separately
asserted recovery records. A future CST walker can neither inspect Error
spelling nor retain parser phase, so it cannot infer the boundary at `3`.

A close node alone is insufficient: the existing Initial, AfterComma and
AfterError positions admit a semicolon as a Separator Error, while ordinary
raw material at the same direct parent is a Field Error. The source role
selection must therefore also be structural before temporary records vanish.

## Approved topology decision

Add two transparent grammar-slot nodes:

```text
NamedRecordTypeSeparator := Missing | Error+
NamedRecordTypeClose     := NativeTrivia* (Error NativeTrivia*)* (RBrace | Missing)
```

The intended XML-like Rowan grammar is:

```xml
<NamedRecordType>
  <LBrace text="{"/>
  <!-- the following direct children may repeat/interleave -->
  <NativeTrivia text="..."/> | <Comma text=","/> | <TypeRecordField>...</TypeRecordField>
  | <Missing/> | <Error text="..."/> <!-- whole Field only -->
  | <NamedRecordTypeSeparator><Missing/> | <Error text="..."/>+</NamedRecordTypeSeparator>
  <NamedRecordTypeClose>
    <NativeTrivia text="..."/>* (<Error text="..."/> <NativeTrivia text="..."/>*)*
    (<RBrace text="}"/> | <Missing/>)
  </NamedRecordTypeClose>
</NamedRecordType>
```

The notation describes structural alternatives, not a new grammar or uniform
list layout. Accepted commas and implicit-newline separators remain direct
native children. `NamedRecordTypeSeparator` occurs once per existing Separator
Missing/Error publication only; it has exactly that recovery occurrence and no
independent diagnostic. Direct `NamedRecordType` Missing/Error remains the
whole-Field occurrence. Existing `TypeRecordField` ordered native
name/colon/Type structure continues to distinguish Name, Colon and RHS slots.

Exactly one `NamedRecordTypeClose` is emitted for every committed record. It
contains the accepted `RBrace`, or the existing zero-width close `Missing`, and
all native close-owned trivia/Error material during its irreversible close
recovery. It has no independent diagnostic. A Close Error followed by a Close
Missing retains two diagnostics from its Error group and direct Missing. A
pending whole-Field Missing stays outside and precedes this close node even at
the same coordinate.

The wrapper range is determined only by its contained tokens/nodes. Separator
Error initial leading is emitted by the sequence before its wrapper; its
Error-internal leading stays Error content. A fresh boundary/ordinary-EOF close
that has not committed close recovery leaves eligible list-leading outside both
the direct Field Missing and the Close node. By contrast, an accepted local
close or an already committed terminal close recovery opens Close before its
close-leading: that native leading, all close Error-internal/terminal EOF
leading and the terminal `RBrace`/Missing stay inside Close in source order.
Protected caller/fence/outer-close Item and its leading remain pending and
outside. No extra parser state, scan, source replay, Error spelling, provenance,
generic recovery facility or Invalid node is introduced.

## Required implementation boundary

The only candidate owner is `type_expr::record::type_record_fields_normalized`:

- the matching local `RBrace` path emits the one Close node around its accepted
  close;
- same-line next-field Separator Missing is enclosed after its existing native
  leading emission; Separator Error likewise emits its initial leading before
  opening its wrapper;
- every existing Separator Error publication, including a fresh semicolon, is
  enclosed without wrapping whole-Field Error;
- mismatched-close recovery opens one Close node only after a pending Field
  Missing has been published, and retains the complete existing close run plus
  its terminal `RBrace`/Missing;
- fresh boundary/EOF close Missing enters the Close node after eligible list
  leading and any pending Field Missing, while the already-open committed close
  recovery retains its terminal EOF leading inside that same Close; and
- generic Field/Name recovery remains outside these nodes.

Do not make an empty layout node, wrap accepted comma, wrap every field,
reclassify/merge records, change current-Item continuation, move direct field
leading, alter Error tokenization or apply these nodes to another record/type
owner.

## Alternatives not selected by this draft

- Close-only topology fixes the demonstrated Field→Close split but leaves
  Separator-versus-Field raw Error ambiguous.
- A wrapper around every Field/Separator/Close creates needless accepted-tree
  topology; direct Field context and existing `TypeRecordField` grammar suffice.
- Uniform accepted separator wrappers introduce unneeded nodes where direct
  comma punctuation already determines the slot.
- `Invalid`, Error nodes, spelling/provenance inspection, expected payloads or
  retaining the parser ledger conflict with governing authority.

## Construction gate

Before implementation, a fresh independent specification review and
compiler/recovery review must validate the full terminal and separator paths.
The user approved both names, the asymmetric separator cardinality, one Close
node for every committed record including accepted records, the described
close-leading ancestor change, and narrow supersession of direct raw placement
only for these existing slots on 2026-09-11.

After approval, use M2: append SyntaxKinds without renumbering existing values;
one implementation/repair bundle; focused tests for Field/Separator/Close
splits, accepted records, source/range/leading/boundary/frozen behavior; one
scoped closure review; package check, format and diff. No benchmark
samples/processes are planned unless material uncertainty appears.

## Construction result

Private M2 construction completed on 2026-09-11. `NamedRecordTypeSeparator`
and `NamedRecordTypeClose` were appended as SyntaxKinds 279 and 280 without
renumbering existing kinds. The owner emits one Close node for every committed
record, with the approved fresh/committed terminal-leading distinction, and
wraps only existing Separator Missing/Error publications. A committed-close
quoted-fence control exposed a pre-existing boundary token-classification panic;
the owner now checks abstract-boundary status before that classification and
hands the protected Item through unchanged. Recovery records, ranges, accepted
grammar and retry/current-Item contracts remain unchanged. Pre-write
specification/compiler reviews, closure and delta review are clean; focused
record tests, the Type-expression module and `cargo check -p yu-syntax` passed.
No benchmark samples/processes were used.

Stop if any terminal route lacks exactly one close child, a Field recovery is
enclosed by Close, range/record facts or current Item change, the field-internal
schema proves ambiguous, accepted syntax changes beyond the approved ancestor,
or a sibling owner would need either node.
