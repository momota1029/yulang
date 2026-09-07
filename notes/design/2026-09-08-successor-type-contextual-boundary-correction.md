# Successor Type contextual-boundary correction

Status: Authoritative; private correction complete

Date: 2026-09-08

Scope: initial TypePathSegment admission and contextual-boundary suspension
inside committed TypeCall delimiters. No lexer, public interface or Type-ML
provenance change.

Approved-by: user through the accepted-input compatibility, reasonable recovery
selection and simplification delegation recorded in
`2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary, under the user's explicit no-subagent direction

## Cause and governing acceptance

The declaration controls for `type T = A::with` and
`type T = A(B with Inner) with {}` stop before their accepted inner identifiers.
The cause is Type ownership, not declaration output or test-harness plumbing:

1. `type_path_tail_normalized` tests caller/outer boundaries before it admits
   the initial name-shaped segment.
2. `type_delimited_normalized` carries `call_outer_boundary` through the whole
   committed Call and into its fresh argument expressions.

The standalone Type grammar admits an Identifier/SigilIdentifier after `::`
with Type-chain trivia. Contextual spellings are not reserved path names.
The direct derives amendment `2026-09-05-direct-type-derives-episode-boundary-amendment.md`
§2 requires fresh Call arguments to suspend TypeOuterBoundary and restore it
after the nested owner returns. Existing declaration acceptance assertions
are retained, subject to separately approved Type-ML separator contracts.

## Selected rule

- At the initial PathSegment slot, a same-line name-shaped Item wins over a
  contextual word boundary. `A::with`,
  `A:: with`, and their `derives`/`via`/`impl` siblings publish no recovery.
  Punctuation, abstract fences and physical-newline contextual boundaries
  remain protected, including a deeper newline. The C14/C15/companion owner
  still receives that complete newline-bearing Item and decides attachment
  or statement handoff. Ordinary noncontextual path names retain their
  existing continuation-qualified newline rule.
  After an actual malformed path Item, existing retry/boundary priority stays
  unchanged; this does not alter its sealed partial-leading operation.
- Once a Call's `(` is accepted, the entire delimiter owner is a fresh nested
  Type scope. Remove its `TypeOuterBoundary` parameter instead of passing and
  suppressing it at individual branches. Initial, separator, item-retry and
  close-recovery phases all use that same scope. Its child Type expressions
  receive `NONE`; the enclosing Call tail retains its caller's value and
  resumes it after the Call returns.
- Explicit `Stops`, actual outer closes, fences, layout rules and Type-ML
  phase/provenance are unchanged. A malformed Call does not speculate about
  whether a future close exists in order to reinterpret an inner name as a
  declaration companion. It recovers locally to an actual close, protected
  caller boundary, or EOF.

This explicitly supersedes the T2b initial-outer-boundary Missing expectation
only when the Item is a qualifying name, and the T3/shared-delimiter tests
that propagate TypeOuterBoundary into a Call. Their typed record shapes,
horizontal ownership, explicit caller/outer-close guards and frozen contracts
remain in force. The T4 inherited Type-ML separator rule is not superseded.

## Selected recovery controls before expectation changes

Ordinary root Type context below has outer `WITH`, no explicit Stops:

| source | consumed source / records |
| --- | --- |
| `A:: with` | complete, no records |
| `A:: =` under outer `EQUALS` instead | `A::`; PathSegment Missing `3..3`; space and `=` pending |
| `T(with` | complete to EOF; TypeCall close Missing `6..6` |
| `T(A with` | complete to EOF; TypeCall close Missing `8..8` |
| `T(A, with` | complete to EOF; TypeCall close Missing `9..9` |
| `T(@ with` | complete to EOF; CallArgument Error `2..4`, then close Missing `8..8` |
| `T(A,@ with` | complete to EOF; CallArgument Error `4..6`, then close Missing `10..10` |
| `T(A] @ with` | complete to EOF; TypeCall-close Errors `3..4`, `5..6`, `7..11`, then close Missing `11..11` |

Records retain the existing full owner/expected/unexpected vocabulary and
source-derived ranges; fresh IDs follow the listed order, frozen IDs are
reused. Appending the matching `)` to the Call controls removes only the
close Missing. Valid `T(with)`, `T(A with)`, and `T(A, with)` have no recovery.
An outer contextual suffix after the matching close is returned to its caller.
The initial-name acceptance controls include both empty and nonempty same-line
trivia and all four contextual spellings. LF, CRLF and newline-bearing comments
before an active contextual word instead retain PathSegment Missing at
`3..3` and return the complete leading-plus-word Item unchanged. This prevents
the acceptance fix from consuming declaration-owned layout.

## Verification and cost

M2 private contract/owner correction, primary-only implementation and checking
per user instruction. Run focused Type and declaration tests; retain unchanged
output/RB evidence and run the package check at the coherent repair boundary.
Pre-write expectations above follow ownership/acceptance, not candidate output.
Known malformed-group continuation and old assertions contradicted by the
already-approved T4 Type-ML rule must be classified separately, not silently
made green. No library feature, rescan, retained state, allocation or traversal
is introduced; removing the carried argument simplifies the hot path. Zero
measurement samples/processes are budgeted.

## Declaration-control classification

Three pre-existing declaration controls are not acceptance authority for this
correction:

- `Head (A with Inner)` and `Head (Eq with Inner)` enter Parenthesized from an
  enclosing TypeApply. T4 therefore owns both inner horizontal gaps as missing
  Parenthesized separators. The no-recovery declaration controls use
  `Head (A, with, Inner)` and `Head (Eq, with, Inner)` instead. These remain
  formally accepted controls for contextual identifiers while leaving the T4
  recovery contract intact.
- In `(Eq::@ = Int) = Body`, the first `=` is an active declaration boundary
  reached after a malformed PathSegment. A streaming owner cannot know that a
  matching `)` occurs later without speculative lookahead. Existing boundary
  safety closes the malformed Parenthesized owner as missing before `=`, after
  which the declaration consumes `= Int` and returns the unmatched `)`.
  The nested-suspension control instead uses `(Eq::@ Int) = Body`: it keeps the
  malformed item and its ordinary continuation inside the committed owner,
  accepts the real close, and returns the unambiguous outer `=` to the
  declaration. The ambiguous malformed case is not inherited from Yulang2 and
  imposes no compatibility requirement.
- The malformed `(A else` explicit-stop control predates the approved shared
  delimiter horizontal rule. Parenthesized owns its one ordinary horizontal
  gap, emits its close Missing after that gap, and returns the raw `else` Item.
  Its committed source is therefore `(A `, not `(A`; accepted syntax is
  unaffected.

## Completion

The private correction is complete. Same-line contextual PathSegments now win
their accepted slot, physical-newline contextual Items remain outer-owned, and
a committed Call gives every argument a fresh `TypeOuterBoundary::NONE` scope
without carrying the enclosing contextual boundary through delimiter recovery.
The shared delimiter retains explicit Stops, outer-close and horizontal-trivia
behavior. No scan, allocation, retained recovery state or public entrypoint was
added.

Focused results: Type 126 passed; TypeDeclaration 39 passed; output 4 passed;
recovery output 25 passed; `cargo check -p yu-syntax`, scoped rustfmt and
`git diff --check` passed. Existing warnings remain. Verification used zero
timing samples/processes and was performed directly by the primary under the
user's no-subagent instruction.
