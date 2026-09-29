# SCC intrusion: conditional graph factorization proof slice

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: reviewed conditional lemma; no implementation authority

## Result

The abstract-semantics draft now states a conditional transport result for an
already prepared member view `H_d`. After root projection has removed
one-sided occurrences, surviving source identities are divided into fresh
member-local identities (`Gen_d ∪ Cycle_d`) and stable identities in `E_d`
(`Free_d`). `Erase_d` is recorded outside the surviving identity set. One
source-keyed `Phi_d` preserves aliases where generalized and recursive roles
overlap.

For an injective per-use renaming, the finite Oracle closure rules commute with
renaming. The proof follows each local closure step in both directions and
preserves constructor, polarity, and variable equality. For separate uses,
fresh local ID sets are disjoint and copied raw edges share identities only
through `E_d`. Closure may derive cross-use obligations through a shared
environment row, such as `a_u <: e` and `e <: b_v`; the draft now states that
explicitly. It does not claim solution-space factorization or principality.

## Review and limits

An independent compiler-referee and spec-auditor reviewed this subsection.
They found and closed issues in the first statement: erasure was incorrectly
included in the surviving-ID partition, satisfaction/principality notation
was undefined, and shared-environment closure could derive cross-use edges.
The final narrow delta review found no remaining findings in scope.

This is not the Gate C theorem. It assumes an exact prepared `H_d`; it does not
prove Oracle edge selection, root/epoch transitions, recursive projection,
source-envelope coverage, or the existence/principality of solutions. The
Oracle identity-use source also remains outside current Yulang3 HIR, as recorded
in `2026-09-29-intrusion-rust-replacement-map.md`.

No compiler code or tests were changed or run for this proof slice.
