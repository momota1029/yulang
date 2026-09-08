# Declaration field sequence current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-09

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Scope: the shared declaration field sequence presently hosted by
`declaration/struct_decl.rs`: required field slots, semicolon separator,
named/tuple matching close, and local mismatched-close recovery, with finite
Struct/Enum/Error role and construct transport.  Its coherent, behavior-
preserving move with field lexical acquisition, boundary predicates, and
candidate classification to `declaration/fields.rs` is part of this gate.
Headers, named-field internals, tuple Type recovery, declaration/variant
sequence ownership, body-introducer recovery, and trailing attachment remain
outside its scope.

Authority: recovery authority §3; typed-output commitments; SD-R's Struct
field table; ENUM-R/ERROR-R's neutral field-driver requirement; the completed
named-field current-Item gate; and the Struct actual-close trailing amendment.

## Finite owner transport

The shared driver receives the following caller-selected identities.  It never
tests a declaration keyword or manufactures a Struct identity for a variant.

| recovery site | Struct | Enum/Error variant |
| --- | --- | --- |
| missing named field | `Struct(Field)` / `Identifier` | `Variant(NamedField)` / `Identifier` |
| missing tuple field | `Struct(FieldType)` / `TypeExpression` | `Variant(TupleFieldType)` / `TypeExpression` |
| malformed semicolon separator | `Struct(FieldSeparator)` / `DelimitedSequenceSeparator` | `Variant(NamedFieldSeparator)` / `DelimitedSequenceSeparator` |
| named close | `Construct(StructNamedFields)` / brace | `Construct(VariantNamedPayload)` / brace |
| tuple close | `Construct(StructTupleFields)` / parenthesis | `Construct(VariantTuplePayload)` / parenthesis |

`Variant(NamedFieldSeparator)` is selected for both named and tuple variant
payload lists.  The established role vocabulary has no tuple-separator role;
this retained historical name denotes the variant payload field-list separator
at this shared site.  It does not assert that tuple fields are named, introduce
a new role, or borrow a Struct role.

## Sequence rule

Every Missing has its caller-selected role, a zero-width site/expectation
range, no unexpected facts, one mapped expectation with
`COMMITTED_RECOVERY_RULE`, and primary index zero.  Every Error uses the
sealed lexical Error-run operation and has one `OtherCharacter` token fact for
each emitted nonempty Item.  Initial sequence leading is emitted by the
sequence owner; internal run leading belongs to Error; retry and protected
boundary leading remain pending.

Matching close has priority.  Protected active stops and abstract boundaries
remain pending before recovery emission or field admission.  Required field
slots and separator recovery use the same lexical-only field observation; they
do not call a grammar parser from Error.  The finite cases are:

| situation | result |
| --- | --- |
| required field at comma or protected boundary | selected missing field; keep boundary pending |
| separator followed by EOF | selected missing field and selected missing close, except an empty open list emits only its close |
| indented trailing comma | valid; no fabricated field |
| accepted field followed by another same-line field without a comma/qualifying newline | selected missing separator |
| malformed separator run | selected separator Error; retry field/close/boundary unchanged |
| absent matching close | selected missing close |
| Struct mismatched close | selected close Error over the maximal lexical run, then retry |
| variant `Borrow` mismatched close | selected missing close and leave the foreign close unread |

No row cascades an additional field, separator, or close record merely because
the preceding row recovered.  Tuple TypeApply remains one Type-owned field;
variant pipe lexical mode and actual-close-only trailing attachment remain
unchanged.

A retry Item that is independently admitted as the next field has its ordinary
separator obligation; that is not a recovery cascade.  Likewise, a mismatched
close Error followed by EOF has one separately required matching-close Missing.

## Topology

Move exactly the owner-neutral field role/list/exit types; delimited and
indented sequence parsers; named and tuple field parsers; field recovery
helpers; field lexical acquisition/boundaries; and next-field candidate to
`declaration/fields.rs`.  `struct_decl.rs` retains Struct header/body choice,
indent-introduction policy, and its trailing adapter.  `declaration_variant.rs`
retains variant sequence and body ownership and adapts into `fields.rs`.
No generic `parser`, `common`, `utils`, or compatibility façade is introduced.

## Evidence and cost

Cover Struct and Enum/Error named and tuple callers, each selected role and
construct close, matching/mismatched/absent close, EOF, active stops, indented
trailing comma, separator runs and retry, pipe lexical mode, tuple TypeApply,
actual-close trailing controls, frozen/seeded coordinates, and accepted
controls.  Run the focused Struct/variant/required-Type/normalized/recovery-
output cone, one package check, format and scoped diff.  Benchmark budget is
zero samples/processes unless material uncertainty appears.  The extraction
adds no source replay, retained token vector, or new traversal.

## Completion

The shared sequence now publishes caller-selected missing field, separator,
and close records, and sealed separator/Struct-close Error runs. Enum/Error
variants select their own payload roles and preserve `Borrow` close handoff.
`declaration/fields.rs` owns the neutral protocol, sequence and field parsers,
recovery helpers, lexical Item acquisition, boundaries, and next-field
candidate; `struct_decl.rs` retains Struct header/body choice, role selection,
and trailing attachment.

The pre-write and delta specification audits closed. Focused Struct (31),
variant (25), and required-Type Equals (5) controls, normalized/recovery-output
(108), package check, format, and diff check pass. No benchmark samples or
processes were used. Aggregate O3b/O4, remaining declaration owners, and
public certification remain outside this completed private gate.
