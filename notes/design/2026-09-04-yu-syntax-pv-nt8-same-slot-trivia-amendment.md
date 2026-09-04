# Authoritative: polymorphic-variant NT-8 same-slot retry trivia ownership

Status: Authoritative

Scope: direct rewrite `PolymorphicVariantType` CST ownership only when an
`NT-8` malformed tag-prefix Error has already opened one recovered
`PolymorphicVariantTag` skeleton and a same-line `NT-6` candidate retries that
same tag. This changes neither `NT` priority nor `NT-safe` membership.

Approved-by: user

Approved-at: 2026-09-04

Reviewed-by: M1 scoped specification review on 2026-09-04

Supersedes: only the general `NT` preamble sentence in
`2026-08-20-yu-syntax-chasa-architecture.md` that assigns every local
`NT-1..6` / `NT-8` same-line leading gap to the direct
`PolymorphicVariantType` CST parent, where that sentence conflicts with an
`NT-8 -> NT-6` same-slot retry.

## Decision

An `NT-8` Error commits exactly one recovered `PolymorphicVariantTag`
skeleton. If its next `NT-safe` point is a same-line `NT-6`
`CanonicalTypePrimary` candidate, that candidate's leading same-line trivia:

1. is excluded from the preceding `Error(PolymorphicVariantTag)` range;
2. is emitted exactly once as a direct child of the already-open
   `PolymorphicVariantTag`;
3. is then followed by the ordinary `NT-6` head outcome in that same tag.

This is a narrow exception to the superseded outer-leading-trivia sentence.
It is necessary because a Rowan child sequence is contiguous: an outer
`PolymorphicVariantType` child cannot appear between an `Error` and a retried
head that must both be children of one `PolymorphicVariantTag`.

No `PolymorphicVariantPayload`, separator, wrapper, source buffer, rescan,
state frame, or second tag is created by this exception. The AST keeps one
recovered tag slot; only direct-CST ownership of this one gap is selected.

```text
:{@ A}

PolymorphicVariantType
  PolymorphicVariantTag
    Error "@"
    Whitespace " "
    Identifier "A"
```

`Error` owns exactly `@`, never the following gap. The tag has a Complete name
and no Missing node.

For a non-Identifier retry candidate, the prefix Error and the `NT-6`
wrong-name Error remain distinct causes and ranges in the same tag.

```text
:{@ 123}

PolymorphicVariantType
  PolymorphicVariantTag
    Error "@"
    Whitespace " "
    Error
      TypeExpression
        Integer "123"
```

The second Error is the existing `NT-6` name Error. It owns the complete
canonical primary, not merely its first token.

## Boundary ownership retained

The exception applies only to a same-line `NT-6` candidate after an already
committed `NT-8` Error. Every other `NT-safe` point remains pending outside
the Error and returns to the ordinary outer `NT` judge.

| Source | Required owner/outcome |
| --- | --- |
| `:{@123}` | one tag; direct tag Error `@`, then direct tag `NT-6` Error containing `TypeExpression(123)` |
| `:{@ ,B}` | the Error excludes the space; outer PV owns the space and comma; comma transitions the recovered tag to the normal unfilled state before `B` |
| `:{@ }` / `:{@ ]}` | the Error excludes the gap; `NT-1` / `NT-2` own the closer and any locally committed leading gap |
| caller-owned close or EOF after `@` | the Error excludes the pending gap; `NT-7` leaves it for the caller and emits only its canonical Missing close |
| `:{@\nA}` | the Error excludes the newline; `NT-5` owns it and creates the next tag boundary |
| `:{@\n  A}` | the Error excludes the newline; `NT-7` returns the deeper newline and `A` to the caller after its canonical Missing close |

`IT-4` remains unchanged. In particular, an accepted tag followed by a
boundaryless malformed byte, such as `:{A@,B}`, hands `@` to `NT-8`; the new
rule affects only the later same-line candidate retry, not payload recovery.

## Verification boundary

The direct rewrite fixture set must prove all of the following:

- `:{@}` creates one Error tag and no Missing tag;
- `:{@` creates that tag plus only the canonical Missing close;
- `:{@A}` retries a normal Identifier in the same tag;
- `:{@ A}` keeps the space outside Error but inside that tag;
- `:{@123 Int}` keeps prefix Error, wrong-name Error, and payload in one tag;
- comma and qualifying-newline continuations after a malformed tag do not
  create a false Missing tag;
- local and caller-owned semicolon/close, plus deeper-newline handoff, retain
  their pre-existing outer owners.

## Implementation status

Implemented in the direct rewrite on 2026-09-04. The `NT-8` scanner opens one
tag-local prefix Error, stops before every `NT-safe` item, and reuses that
same tag for a same-line `NT-6` candidate. The direct implementation carries
no persistent recovery state, source retention, or rescan; `IT-4` remains
deferred. M1 scoped specification review approved the code and fixture scope.
