# Error-admission schema clarification

Status: Draft

Date: 2026-09-09

Scope: declarative CST admission of malformed source in the successor parser.
This clarification makes the per-slot schema requirement of the CST-derived
diagnostics amendment explicit. It does not add accepted source syntax, change
recovery continuation, broaden `Invalid` ownership, alter the topology-only
migration, or authorize a parser/API implementation.

User direction: malformed input is not admitted indiscriminately. A production
specifies the locations and sequences in which its lossless CST may contain
recovery elements, allowing an error-containing CST to be structurally
accepted with finer control than an untyped recovery wrapper.

## Decision proposal

An error-containing CST is structurally admitted only where the owning
production's documented grammar slot allows its exact sequence. Structural
admission means that parsing can produce one lossless CST with explicit
malformed elements. It does not make the original source recovery-free
accepted syntax, and it does not establish downstream HIR, type-checking, or
execution behavior for malformed input.

The schema is ordered and context-sensitive. A slot identity consists of its
containing production, ordered phase/child position, and any documented
ancestor context needed to distinguish it. A parent kind alone is insufficient.
The schema must identify a slot from the CST structure and its documented
context without parser recovery records, opaque-Error relexing, or hidden
provenance.

For every recovery-bearing slot, the production schema records:

| Required fact | Meaning |
| --- | --- |
| ordered child grammar | valid children, optionality, repetition, punctuation, and phase order |
| admitted malformed sequences | whether the slot permits `Missing`, a raw Error group, a retry after that group, a terminal group, or a structured child |
| child ownership | nested grammar that remains owned by a child production and may therefore contain its own admitted recovery |
| source ownership | punctuation, ordinary trivia, malformed-run trivia, and protected-boundary leading |
| diagnostic projection | expected alternatives/primary expectation where applicable, recovery category, and occurrence order |
| slot context | all ancestor/phase facts needed for unambiguous interpretation |

Omission grants no malformed admission. A blanket union such as `Valid |
Missing | Error | Invalid` is not a schema: it cannot express ordering, retry,
boundary preservation, or diagnostic grouping.

## Recovery elements and containment

`Missing` is a zero-width absence admitted at a documented required slot. An
optional absence normally emits no `Missing`. A schema explicitly decides
combined expectations, consecutive same-offset `Missing` occurrences, and any
case where one malformed episode suppresses a same-cause absence.

A raw `Error` group contains nonempty physical source fragments in one
documented slot. Its adjacent token leaves form one group only while they have
the same immediate parent and slot. A schema states whether a valid retry may
follow it, whether it is terminal, and which leading/trailing trivia and
boundaries remain outside the group.

`Invalid` retains structured wrong-slot recovery that contains nested grammar,
`Missing`, or nested raw `Error` groups. This clarification retains the existing
restriction: only polymorphic-variant TagName recovery and record-pattern
wrong-kind Item/Separator recovery may introduce `Invalid`. Their nested
children follow their own documented schemas. A valid enclosing node does not
gain an outer `Invalid` merely because it contains an admitted malformed
descendant.

No production gains a new structured owner, an extra `Invalid`, a changed
continuation, or a changed boundary rule by analogy. Such a case requires a
separate Authoritative amendment.

## Diagnostic interpretation

The existing CST-derived diagnostic rules remain unchanged:

- a `Missing` occurrence emits the documented slot's missing diagnostic at its
  zero-width UTF-8 byte range;
- a maximal adjacent raw `Error` group in one immediate-parent slot emits one
  malformed-input diagnostic over the combined group range;
- an `Invalid` occurrence emits its structured diagnostic before its children;
- environment conflicts are derived at a complete `OperatorHeader` occurrence
  and never mutate the CST.

Slot boundaries must not split physically indistinguishable adjacent Error
fragments merely to obtain a desired diagnostic count. If CST structure and
schema context cannot determine the slot uniquely, the owning CST schema is
incomplete and blocks retirement of parser diagnostic state.

## Compatibility and boundaries

This clarification does not change the approved topology-only gate. Until the
complete per-slot schema and its later migration are complete, existing parser
recovery records, structured reservations, frozen-header reconciliation,
diagnostic IDs, public diagnostic construction, and their temporary extents
remain compatibility machinery exactly as already specified.

It does not change accepted syntax, source losslessness, current-Item/fence
handoff, outer-boundary preservation, or recovery continuation. It introduces
no schema DSL, code generation, runtime validator, new public API, parser
ledger, or second tree.

## Public-reference form

Each reconstructed construct page presents its accepted surface spelling and
source-order Rowan schema. Where the construct has admitted malformed forms,
its EN/JA pair records the relevant slot sequence, punctuation/trivia and
boundary ownership, and diagnostic placement. It does not expose parser
control flow, commits, fixtures, or implementation provenance.

The internal design schema may use a compact slot table beside XML-like Rowan
examples. Public pages use the existing XML-like notation and explanatory
grammar; they do not reproduce a compiler-internal coverage ledger.

## Representative schema slice: AssignmentTail inline RHS

### Authority and boundary

Status: Authoritative for this direct-inline slice only

Approved-by: user

Approved-at: 2026-09-10

The user approved this slice after its focused Rowan evidence and independent
specification and compiler/recovery audits. The approval covers the concrete
child topology, leading ownership, recovery admission and diagnostic
projection stated in this section. It does not promote this document's other
proposal material, the delegated `IndentedStatementBlock` alternative, any
other slot, the inventory, CST interpreter, parser-ledger retirement or public
diagnostic API.

The direct inline `Assignment(Rhs)` position of `AssignmentTail` is the first
specified slice for this clarification.
Its governing authority is
`2026-09-09-successor-expression-structural-tails-draft.md`, **Owner topology
and admission** and **Assignment**; its M2 construction handoff confirms the
flat tail topology, one-character acquisition, one RHS, terminal exit, and
focused recovery verification. This is evidence for the schema method only. It
does not make other expression slots complete or infer their malformed forms.

The ordered direct-inline CST alternatives are:

```text
OperatorChain := <left-expression children and pre-`=` trivia> AssignmentTail
AssignmentTail := Equals (Missing | Error+ | Error+ OperatorChain | OperatorChain
                          | <delegated IndentedStatementBlock>)
Equals := "="
```

This grammar elides trivia only to make the child alternatives legible. Initial
leading before both an accepted and an initially rejected direct RHS is native
trivia directly under `AssignmentTail`, before its `OperatorChain` or raw
Error children. Leading at an admitted retry is instead native trivia in the
new `OperatorChain` child. The boundary/missing rule owns only the leading it
explicitly selects.

`AssignmentTail` never owns or wraps the left expression. In the accepted
direct alternative, and after a raw-group retry, the RHS is a concrete
`OperatorChain` child; `InlineRhs` is not a Rowan node. A raw group is direct
`Error` token children of `AssignmentTail`. Its initial rejected-Item leading
is direct `AssignmentTail` trivia outside the raw group. The tail is admitted
only at the outer, enabled non-ML continuation after an admitted dynamic LED
has declined; lower-threshold and ML candidates have no source, CST, or
recovery effect. This representative proof covers only that direct-inline
alternative.
The deeper-line alternative delegates to the existing
`Assignment(IndentedStatement)` block contract with a concrete
`IndentedStatementBlock` child and a `Statement` expectation; its block-entry
and child-slot schema remain an explicitly open dependency rather than an
implied recovery-free child.

For the direct inline slot, both `Missing` and one maximal raw Error group
project `Assignment(Rhs)` with expected `Expression` and primary index zero.
The raw group is one malformed-input occurrence for this slot, not a parser
unexpected payload or a second Missing. In both raw alternatives below,
initial rejected-Item leading remains outside the raw group, interior leading
belongs to it, and leading before an admitted retry or a protected boundary
remains outside it according to the direct-child placement above.

| `Rhs` sequence | Structural admission and ownership | Diagnostic / continuation fact |
| --- | --- | --- |
| inline `OperatorChain` | one required direct inline child | no recovery element |
| required RHS absent at an admitted stop, boundary, separator, close, non-NUD bracket opener, non-continuing layout, or EOF | one zero-width `Missing` in `Assignment(Rhs)` | expected syntax is `Expression`; protected Item/leading stays pending; ordinary EOF may first emit owner-leading and anchors at physical EOF |
| non-boundary non-NUD run followed by an admitted inline expression | one nonempty direct raw Error group, then one `OperatorChain` child | expected syntax is `Expression`, primary zero; one malformed episode retries the same Rhs position; nested recovery retains its own grammar-owner slots within the RHS child |
| non-boundary non-NUD run reaching a protected boundary | one nonempty terminal raw Error group | terminal raw group returns the boundary unchanged and adds no same-cause `Missing` |

The current temporary parser-record compatibility path distinguishes an
abstract-boundary record anchored at its inspected coordinate, another
protected-boundary record anchored at the remaining Item start with that
complete Item and its leading unread, and the ordinary-EOF rule in the table.
Those record anchors do not relocate the structural `Missing` occurrence. In
the later CST-derived diagnostic migration, its missing diagnostic uses that
node's zero-width CST range as already specified by the governing amendment;
the current record-coordinate compatibility is then retired rather than
preserved as hidden schema provenance.

The raw group uses the implemented Error-token/Invalid-node topology; it does
not authorize an `Invalid` child. The table's ordered alternatives, concrete
direct children, leading placement, direct-tail ownership, and boundary facts
distinguish the Rhs slot without parser records. It also shows why a generic
`Error` child union would be inadequate: the two raw cases have different
following children and protected-boundary behavior.

Draft evidence for this direct-inline slice is complete as of 2026-09-10:
focused Rowan assertions cover accepted RHS, protected Missing, terminal Error,
Error-to-retry with retry-leading ancestry, a contiguous multi-fragment Error
group, and nested FieldTail Missing ownership. Specification and
compiler/recovery delta audits found no remaining slice finding. This records
evidence for the Draft only; it neither promotes this slice nor closes the
indented dependency, complete inventory, interpreter or parser-ledger
migration.

## Construction and proof gates

1. Independently review the representative direct inline `Assignment(Rhs)`
   slice above for exact direct-child topology, leading placement, expected
   projection, malformed sequence, continuation, range and boundary
   preservation. Add exact CST evidence for accepted RHS, Missing, terminal
   raw Error, Error-to-retry with retry leading, and nested recovery. No parser
   change occurs in this gate. A clean review and that evidence close only this
   representative direct-inline proof, not the indented-block dependency or
   the whole-slot inventory.
2. Inventory every recovery-bearing slot and publish its ordered schema before
   the existing parser-ledger/public-diagnostic migration. An unmapped slot
   remains explicitly open; it is not inferred from a parent kind or current
   output.
3. Reconstruct public construct pages one EN/JA pair at a time from an
   Authoritative schema slice and an implemented-gate handoff. Compare only the
   specified CST topology; return an unresolved slot or API choice to the
   primary.
4. Preserve the existing topology-only Error-token/Invalid-node gate and its
   compatibility state. Complete the already-authorized full CST-derived
   diagnostic migration only after the slot inventory closes.

Verification for a schema slice covers accepted input; Missing and combined
same-offset cases; malformed-then-valid retry; terminal malformed input;
adjacent raw groups across slot boundaries; nested `Invalid`, `Missing`, and
`Error`; valid syntax inside `Invalid`; UTF-8, CRLF, and Yumark fragments; and
protected boundary preservation. Stop the affected gate if a required
diagnostic needs hidden parser facts, a slot cannot be uniquely identified, or
a proposed form changes existing continuation or source ownership.

## Relationship to existing authority

This document clarifies the CST-derived diagnostics amendment's requirement
that every recovery-bearing slot have ordered child grammar and recoverable
context. It retains the Rowan CST-only amendment's lossless direct-tree model
and the topology-ordering addendum's two-owner `Invalid` restriction. It
supersedes nothing on approval.
