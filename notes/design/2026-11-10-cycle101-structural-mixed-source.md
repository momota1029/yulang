# Cycle 101: checked structural source and mixed closure

Status: Draft implementation correspondence, 2026-11-10. No new language decision.

## Objective and boundary

Close the finite structural-source version of the cycle 100 mixed closure: compute
slots and identity atoms from named occurrences, rather than ask callers for an
arbitrary Source map, and relate the actual solver to independent source-name
judgments. The existing checker supplies placeholder scope, arity and associated
name validation. Spec 6.3 governs shared associated equalities and conjunction.
Scope-resolved names, finite occurrence selection, old grammar-valid state and the
role registry remain inputs. Parser adequacy, dynamic allocation, invocation
identity and full B4 are not established.

## Data and independent statement

For any structural Program p, State (table p).length s, checked env/roles, and any
assignment v, actual completed atoms hold iff s holds and there exists one source
valuation factoring v through the computed table and satisfying every named
Derives fact. Derives has only initial explicit scalar evidence, transfer along
original reciprocal ordinary edges, and structural materialization plus independent
role/associated declaration derivation. It does not call the executable closure.

The executable path computes source(compile p), extends s with physical type-only
identity atoms, then calls mixed saturation. Source identity atoms constrain even
classes with no scalar seed. No effect equality is introduced.

## Proof chain

1. Prepared reciprocal edges are exactly original reciprocal edges or same-name
pairs. Identity preparation adds no scalar evidence.
2. Induction both ways between allocated mixed derivations and named structural
Derives, using the pre-existing structural step theorem.
3. Existing mixed exactness plus source factorization gives final evidence and
all-model correspondence, then actual ordinary solver acceptance.
4. Existing raw checker preserves the input occurrences and computes the checked
program. A successful check is not evidence of ordinary consistency.

The finite fact bound is 8 * p.length, computed from two positions per occurrence
and four scalar facts per position. General fair scheduling and dynamic children
are outside this claim. The B4 main theorem still needs the same five bridges.
