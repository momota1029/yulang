# SCC intrusion conditional projection-isomorphism lemma

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: conditional lemma; Oracle/intrusion state relation unproved

## Lemma added

The abstract-semantics draft now states a query-isomorphism sublemma for one
frozen projection snapshot. A sort-preserving bijection maps semantic
identities and their supports, formulas, incidences, coverage roots, carriers,
premises, row states, and validity dependencies. The relation preserves the
evidence/ordinary lanes and their stored order, canonical cursor order,
preflight traversal/error precedence, formula revision and structural snapshot
validity, and projection-round evaluator/memo/cycle state. Equal resource
failure behavior is an explicit premise.

Under these conditions, corresponding calls to the scoped query return the
same `Included`/`Unclaimed`/`Excluded`/failure class, with evidence payloads
mapped by the bijection. The proof is lockstep simulation over ordered record
enumeration, preflight, canonical formula arms, mapped recursive calls, memo
hits and cycle cuts; the first included arm therefore corresponds. This does
not construct the bijection for real Oracle/intrusion states, prove mutations
preserve it, or establish public parity.

## Evidence and review

The source map in
`notes/progress/2026-09-30-intrusion-projection-order-map.md` records the
Oracle details. The crucial branch is first-included canonical formula
selection: proof identity allocation can affect evidence, so a plain variable
renaming is not enough. The conditional lemma requires preservation of
canonical order and proof validity instead of assuming IDs or outcomes match.

An independent compiler-referee delta review found no blocking or major issue.
It confirmed that the premises cover the inspected bound enumeration,
preflight/canonical order, first-included evidence, memo/cycle state, terminal
latches, and resource-failure outcomes. The review did not audit every proof
evaluator branch or a full Oracle-to-intrusion trace. Constructing the required
order-preserving relation across actual root transitions remains open.

No compiler code or tests changed or ran. No Python or measurements were used.
