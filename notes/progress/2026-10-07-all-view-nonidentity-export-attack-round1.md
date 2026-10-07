# ALL_VIEW nonidentity export attack, round 1

Date: 2026-10-07
Baseline: `b9ffbfc20f1cbd71f2b5deccea6ee8a033d55ceb`
Claim class: bounded constructor and evidence audit
Authority and production effect: none

## Target and starting status

The current target was actual acceptance at the submitted designated
`B_common` of a checked nonidentity public Function view, correlated with one
original source/query witness and complete resolver/admission evidence.
`ALL_VIEW` was OPEN-PROOF and `PRINCIPAL` CONDITIONAL-CLOSED. The investigation
avoided the exhausted Integer/Top example and targeted a whole-tuple union
route.

## Union route

For a Name-result source such as `my id x = x`, hold fixed the original value
`z`, witness `w`, scopes, tuple `xi=(nu,K,D)`, paths and lineage. The source
contracts' independent logical interpretation of relation union gives:

```text
R_A(z,w;xi) => (R_A union R_C)(z,w;xi)
```

That does not establish that `B=A union C` is an independently licensed
value descriptor for this Name or that its `DescMem` interpretation is this
relation union. For this exact candidate, the missing formation obligation is:

```text
original value-union descriptor formation and interpretation, at the fixed
  source Name occurrence, scopes, witness and xi
---------------------------------------------------------------- [missing]
DescMem(B,z;xi,w) iff DescMem(A,z;xi,w) or DescMem(C,z;xi,w)
```

Typed-core Name/Lambda skeleton rules do not introduce that endpoint. The
checking rule assumes `VIncl`; it does not derive the source relation from a
solver operation. Source-contracts §2.2 supplies `DescMem` independently.
Therefore calling relation union a value endpoint would assume the missing
constructor for this candidate. This equality is not the minimum requirement
for every nonidentity view: in general, the needed leaf is independent
formation/interpretation of `B` plus same-decoration inclusion
`DescMem(A,z;xi,w) => DescMem(B,z;xi,w)`. A separately licensed conservative
descriptor may satisfy that inclusion while containing other values. The
present route neither forms its proposed union endpoint nor supplies an
inclusion proof usable by a source-checking rule.

There is a second, downstream evidence obligation. Source-contracts §5.3
gives union injection for coverage certificates. Its displayed relational
`Le-C` compares matching constructor tags and operands; it does not itself
provide arbitrary finite `Le(F, union(F,G))`. Even if both a source endpoint
and finite inclusion were supplied, acceptance of a changed whole-Function
result interface would still need an applicable original resolver/checking
clause.

## Separate returned-Function guarantee route

Source-contracts §4 conditionally derives `Cov(E,W) => Bound(E,u) => Bound(W,u)`
for the same complete provider and all admitted finite future interactions.
This avoids assuming an Int/Top relation. An actual source instance still
needs an original `DescMem` decomposition exposing the eligible guarantee at
its source incidence. The `higher` applicability table does not state that
descriptor/checking constructor. This route therefore stops at the same
independent source-formation boundary.

Widening `W_public` does not introduce the missing endpoint. Paired Option 2
grammars preserve the base and envelope evidence they receive, including
unanchored extras; they do not supply that evidence or establish resolver
acceptance at `B_common`.

## Implementation cross-check and result

The current implementation has `admit_lambda_fact` feed the body value into
the Function result, compares Function endpoint pairs, and can construct a
`positive_union` during finalization. That finalizer operation is not source
checking evidence or an acceptance derivation for successor `B_common`.
This bounded inspection establishes no universal resolver-absence claim.

No concrete accepted `Direct(B_common,R_V)` instance, source counterexample,
or complete alternate semantics was constructed. `ALL_VIEW` remains OPEN-PROOF
and `PRINCIPAL` remains CONDITIONAL-CLOSED; counts and edges do not change.
The next attack should derive or refute the original value-union
descriptor/checking constructor at the returned Name incidence, then show
which actual-root resolver case consumes its finite inclusion evidence.

## Scope and checks

The producer compared 12 governing semantic/policy/code dependencies against
the pinned baseline and found them byte-equal. The assigned DAG section was
also read from the pinned tree; its concurrent task-level update did not
change `ALL_VIEW` or `PRINCIPAL`. Inspection was bounded and read-only. No
tests, builds, executable probes, Oracle execution, writes, Git mutation,
performance measurements, or production changes occurred. No independent
review is claimed for the producer's derivation. A compiler-referee review
found one minor overstatement: the exact `DescMem` equality applies only to
the selected union candidate. The note was repaired to state independent
`B` formation plus same-decoration inclusion as the general leaf; delta review
passed with no further findings. The reviewer did not reproduce producer
dependency hashes or certify production conformance.
