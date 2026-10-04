# Successor meaning of role-indexed effect-row components

Question ID: `function-effect-row-denotation`
Question revision: `q1`
Predecessor/history: none; follows the approved production Function-denotation basis in `../2026-10-05-production-function-denotation/`
Original worktree: `/home/momota1029/rust/yulang`
Branch: `research/simple-sub-intrusion`
Relevant source revision(s): `c3fe10151e6e73fda428ade0a30224cecfd8bb4b`
Task/thread locator: unavailable: no stable conversation locator is exposed
Governing source/section: `notes/design/2026-10-03-concrete-compatibility-boundary.md` §§3–8; `notes/design/2026-10-02-ordinary-computation-semantics-package.md` §§2, 4–5; `notes/design/2026-10-02-typed-computation-core-elaboration.md` §9; `notes/design/2026-10-03-callback-context-delivery.md` §§2–4; `syntax-reference/en/src/types/effect-row-type.md` §1

## Requested scoped decision

Select the intended source meaning of a mixed effect-row descriptor after the
Function introduction/expected-context role and complete typed port have been
chosen. The narrower question is how abstract row components and concrete
typed effect records constrain that port, and how they combine without losing
the original `Rel_C`, `nu,K,D`, occurrence, path, attachment, or handler-image
evidence.

This question does not select a parser spelling, inference algorithm, new
carrier, or production implementation. It does not reopen B callback literal
generation, the approved production denotation basis A, the single
endpoint-dependent `A <: B` solver, or the existing Pure-value callback-slot
view.

## Background and current premises

The user's selected source order is:

```text
function introduction + expected context
  -> receiver role and boundary
  -> Function interface and typed port
  -> interpretation of that port's effect descriptor
```

The user also selected canonical flat covariant rows, abstract components plus
concrete components, same-class co-occurrence consolidation, and only partial
contravariant reverse addition when the concrete contribution and its
attachment are known. A concrete subtraction cannot erase another event of
the same family when the complete handler image or raw continuation still
exposes it.

The approved production denotation basis selects the existing complete typed
observation relation `Rel_C` at fixed `(nu,K,D)`, with descriptor membership
and challenge admission interpreted independently of the concrete comparison.
It does not select the predicates that interpret individual effect-row items.

The current concrete-compatibility draft already states two conditional
reduction candidates (§§7–8):

- a resolved concrete item `tau = F(args)` may test the typed family point of
  an already-existing request occurrence;
- an abstract component `alpha` may denote a complete correlated view at its
  role-derived typed port;
- at a fixed jointly admissible fiber, a covariant support projection may be
  the union of abstract-view support and concrete family points, while the
  full relation retains the common tuple and separate incidences.

Those are explicitly conditional because annotation elaboration does not yet
map row occurrences to the existing view/incidence, and no component
combination rule has been selected. Syntax authority defines row delimiters
and items, but excludes row-tail meaning, lowering, and effect inference.

The recent finite handler probe supplies one discriminator: an input sequence
can produce two distinct `tick` events from the same source flow; a shallow
handler may consume the first and resume its raw continuation, leaving the
second `tick` in the outward complete image. Support-wide deletion of the
family is therefore insufficient evidence for subtraction. This probe does
not define the row annotation meaning.

## Candidate choices and consequences

### A. Role-indexed component allowance with a joint fiber (candidate)

After role and port selection, interpret a row as a support allowance over
already-existing typed request occurrences:

- each concrete `F(args)` item covers the matching typed family point of an
  occurrence; it does not construct an event or identify events sharing that
  family;
- each abstract component denotes its source-linked port view in the same
  `Rel_C` fiber, retaining dependent request, continuation, and value
  coordinates;
- covariant row combination is union at the support projection only. The
  complete membership predicate keeps all component constraints and evidence
  joined under the same `(nu,K,D)`; it does not take an independent Cartesian
  product;
- contravariant concrete-bearing structure is a partial reverse-addition
  descriptor. A concrete contribution may be reversed only at its witnessed
  attachment and only when the complete source image justifies that
  contribution's removal. Abstract components are not canceled by a family
  support calculation.

This gives a direct target for a comparison-independent descriptor-membership
rule and keeps the user's role-first order. It still requires a source
annotation-to-path/occurrence derivation and proof that the chosen same-fiber
combination is principal and sound. It is not an implementation decision.

### B. Complete-view relation per component, with no support-allowance rule

Treat each row component only as a name for an independently established
complete view. Combination would be defined directly on those relations, with
no pointwise family-support interpretation for concrete items.

This avoids selecting a support predicate, but the current source documents do
not identify what complete view a concrete `F(args)` item names. It would need
an additional source rule for concrete components and a combination operator;
without them, endpoint membership remains non-executable and no progress is
made toward the production gate.

### C. Another component meaning

Specify a different interpretation, including how a concrete item, an
abstract component, and multiple row components jointly constrain a
role-selected typed port. Any proposal must preserve per-event identity and
attachment, and state where the original `Rel_C` fiber is kept.

## Affected work

Blocked scope: defining the comparison-independent mixed-component
`DescMem_A` rule, deriving the production endpoint/role/path membership clause,
and proving actual-to-checked containment for this effect-row fragment.

Independent authorized work: structural FMP results, existing bounded
research checkers, pure structural prototype work, and documentation of
already-settled source contracts.

Required answer: select A, select B, or give the intended alternative under C.
Approval here would select only the semantic target for this descriptor
fragment. It would still require independent design review and recording in a
governing design before implementation.

Pending publication: keep this entire question directory unstaged and uncommitted
until the questioning primary discovers and validates an explicitly approved
local answer and commits the matching question/draft/answer together. The
answering primary never mutates Git. Posting does not pause the goal; dependent
work waits while independent work continues on disjoint owned paths.
