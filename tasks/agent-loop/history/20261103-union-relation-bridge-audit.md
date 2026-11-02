# Union relation and type bridge audit

At baseline `24e8ffc2d79a4ffa57e9b9ce51e06d8e9d530337`,
`/root/union_relation_bridge` inspected three distinct constructions:
source-contracts §2.1 relational whole-tuple alternative (proof notation before
a source translation); `SimpleSubConstraintSyntax.Term.union` and its join
rules; and the auxiliary `Catalogue` / `Relations.alternative` packet model.
No identification among these was found in the bounded inspected sources. This
is not a repository-wide absence claim. Production `PositiveValueView` and
`positive_union` retain member ranges; no runtime branch selector follows.

The lattice union elimination and introduction rules allow both derivations
for an overlapping member and impose no unique choice. The bounded `atomView`
model interprets union with disjunction. These are definition-based observations,
not a newly checked source-language theorem.

The raw auxiliary catalogue admits arbitrary port and dependent packet types.
For an inhabited child catalogue and an independent result catalogue with
`Port := Empty`, a child packet exists but a result packet cannot exist, even
when an unrelated whole-tuple disjunction is inhabited. Therefore generic
union membership alone cannot supply a total child-to-result packet function
for arbitrary catalogues. The actual `Relations.alternative` may be empty and
its constructors already require a result packet and relation witness; the
example refutes neither those constructors nor union semantics. It is not a
source-reachable counterexample: authentic source formation may constrain the
catalogues.

Independent `/root/union_semantics_audit` checked these definitions and returned
PASS for the distinction and raw-model observation with these qualifications.
Neither reviewer ran Lean or tests; neither wrote files. Remaining work is to
locate the actual source translation, derive its catalogue compatibility and
dependent transport or repair an unnecessarily strong auxiliary representation.
R159 and the dependent correspondence remain open; no semantic change follows.
