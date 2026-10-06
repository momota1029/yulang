# Bounded shadow equality-orbit evaluator

Date: 2026-10-07 (session UTC date 2026-10-06)
Baseline: `ad514061de2792c374a4b5c224dff7f4772906e8`
Status: independently reviewed shadow implementation; eight focused tests passed
Review and executed evidence: [round-2 integration record](2026-10-07-successor-round2-review.md#scoped-atom-evaluator-follow-through)
Scope: default-off shadow utility, no source/type/world semantic authority

## Governing invariant

The primary's authorized packet applies the independently passed restricted
orbit theorem in `2026-10-07-successor-effective-projection-round2.md` §§2–3.
This utility evaluates a caller-supplied finite equality/disequality formula
for one specified public equality valuation over an infinite uninterpreted
atom domain. The original quantifier tree is evaluated directly. Every binder
has one globally unique syntactic ID and all its occurrences share its current
atom class. No prenexing or independent witness copies are introduced.

Public `u64` labels are opaque equality inputs, normalized by first occurrence,
not numeric order. At each binder the evaluator considers every currently
fixed public/bound class and one new class outside that finite support. The
new class is internal: there is no finite actual-atom universe cutoff.

## API and resource contract

`Formula` admits only Booleans, equality, disequality, negation, binary
conjunction/disjunction, and explicit existential/universal atom quantifiers.
`AtomRef` refers to a public port index or a lexically enclosing binder ID.
There are no callbacks, semantic predicate escape hatches, worlds, or recursive
formula operators. A separate full prevalidation pass checks both Boolean
branches, lexical scope, public indices, and binder uniqueness across all
branches before evaluation can return truth.

Structural bounds are 128 formula nodes, depth 32 (root depth one), 16 total
binders, and 16 supplied public ports, including duplicate labels. Each
visited evaluation node consumes one caller-supplied budget step. Quantifier
body visits are charged separately per representative. Shortcircuiting is
allowed only when the Boolean/quantifier result is already established.
Resource failure returns `Error::Exhausted`, never an approximate truth value.
Structural exhaustion may precede discovery of a later malformed subtree.
Caller-owned formula construction/destruction is outside these bounds.

## Tests supplied, not executed by this worker

Tests cover quantifier alternation, a shared correlated witness, repeated
occurrences, freshness outside sixteen distinct public constants, nested
lexical values, escaped/sibling references, duplicate binder IDs in nested
and separate branches, invalid references hidden behind a true branch,
public-label/binder-ID renaming, justified shortcircuiting, evaluation budget,
and each structural bound. The primary owns module registration, compilation,
and test execution. No test result or independent implementation certification
is claimed here.

## Explicit omissions

This is pointwise equality-only projection evaluation. It generates no public
scheme or residual formula and exports no witness strategy. It does not decide
full arbitrary residual projection, atom freshness eligibility, Generalize,
source signatures, type constraints, descriptors, independent world admission,
recursive semantics, all-valid-view Function principality, or source acceptance.
No production route is changed. Integration and review remain primary-owned.

Exclusive worker paths: `crates/yu-core/src/shadow_atom_orbits.rs`,
`crates/yu-core/tests/shadow_atom_orbits.rs`, and this note. The primary owns
`crates/yu-core/src/lib.rs`, all builds/tests, and Git integration.
