# R18 variant raw-to-paper correspondence — proposal docket v1

Status: **UNADOPTED; approval required from the governing semantic owner.**
This docket prepares the OPEN request `R18-VARIANT-TYPEARG-CORRESPONDENCE-1`
for authority review. It does not select an interpretation or revise any
source, paper rule, raw syntax, typing judgment or proof contract.

## Frozen evidence

The manuscript uses `t(\bar v)` in the raw value grammar (:150–155) and types
it at :219 by matching the constructor tag and ordered payload arity/types in a
declared variant row. It supplies no separate type-argument list on this value.
The sentence at :109 retains constructor/payload type arguments generally, but
does not define the Lean field's correspondence. The original simultaneous
substitution claim (:953–977) requires every included type-bearing component
to receive the same σ.

Lean raw syntax is
`Value.variant constructor typeArguments payload`; `mapPaperValue` maps
`typeArguments` independently from the ordered payload list. `VariantFormed`
validates row tag uniqueness and payload-type formation, but has no raw value
argument. The inspected HIR and playground source/runtime paths carry tag and
ordered payloads without this extra field. Full hashes and scoped findings are
preserved in `r18-variant-authority-intake.md`.

Discriminator retained from the R18 frozen handoff: a fixed non-head row tag
with two payload component types and ordered payload values can be paired with
either an empty extra raw list or a singleton unrelated type. The manuscript
rule does not decide the relationship. Neither raw value is asserted typed or
rejected here.

## Alternatives requiring an authority decision

Each item is a proposal only; this docket endorses none.

1. **Remove the extra field** from raw variant syntax so the raw object matches
   `t(\bar v)`. This changes the Lean raw domain and dependent map/substitution
   consumers, so it requires explicit source/domain approval.
2. **Retain it as inert metadata.** An approved rule must say that it cannot
   affect typing or row selection and specify its preservation under σ. This
   is a semantic claim, not a consequence of the current syntax mapper.
3. **Tie it to declared constructor parameters.** The owner must identify the
   authoritative declaration instance, its type-parameter arity and how the
   ordered row payload types are obtained from that same instance.
4. **Require a canonical/equal representation.** The owner must state which
   exact list is canonical and prove that this retains the original supported
   source domain; payload component types and constructor type parameters must
   not be conflated.
5. **Other correspondence.** The owner must give a formal relation between raw
   values, row entries and their substitution actions, with the same source
   scope and discriminator coverage.

## Required approval packet

The semantic/source authority owner should select or replace an option with a
versioned rule and provide: (a) the governing source and exact changed claim,
(b) raw-to-paper value and ordered payload mapping, (c) identity and arity
conditions, (d) the single-σ action on row, extra field and payloads, (e) the
status of the two discriminator values, and (f) dependent syntax/map/proof and
source/native owners. An independent reviewer must check scope preservation and
that no type information is silently dropped or invented.

Until that approval exists, R18 remains `STOPPED_AUTHORITY_BLOCKER`; no variant
typing constructor, equality/emptiness/metadata semantics, raw-domain change,
or dependent production work is authorized. Independent paper rules such as
template invocation may proceed under their own exact contracts.
